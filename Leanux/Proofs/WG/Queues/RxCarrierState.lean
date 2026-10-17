import Leanux.Proofs.WG.Packets.RxOriginCuts
import Leanux.Proofs.WG.Origins.IndexMaterial
import Leanux.Proofs.WG.Queues.RxPollPrimitives

/-! Local RX peer-credit accounting. The finite carrier and reservation ledgers
are supplied explicitly; no reservation is manufactured from reference-count
slack. Inventory, queue occurrences and numeric protection are separate.
These definitions do not assert initialized reachability or ring conservation. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
set_option pp.structureInstances false

structure Owner where
  epoch : Nat
  slot : PeerId
  stamp : Nat
  deriving DecidableEq

structure Packet where
  epoch : Nat
  slot : SkbId
  deriving DecidableEq

inductive Phase where
  | unpublished | queued | selected | paid
  deriving DecidableEq

def Phase.charged : Phase → Bool
  | .paid => false
  | _ => true

structure Carrier where
  packet : Packet
  owner : Owner
  phase : Phase
  deriving DecidableEq

abbrev Ledger := List Carrier
abbrev Reservations := List Owner

def resident (w : WGWorld) (o : Owner) : Option Peer := do
  let d ← w.dev
  if d.ifindex != o.epoch then none else do
    let p ← d.peers[o.slot]?
    if p.internalId != o.stamp then none else some p

def balance (w : WGWorld) (o : Owner) : Nat := ((resident w o).map (·.refcount)).getD 0

def charges (cs : Ledger) (o : Owner) : Nat :=
  (cs.filter fun c => c.owner == o && c.phase.charged).length

def demand (cs : Ledger) (loans : Reservations) (o : Owner) := charges cs o + loans.count o

def Protected (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  ∀ o, demand cs loans o ≤ balance w o

def packetAt (w : WGWorld) (p : Packet) : Option RxPacket := do
  let d ← w.dev
  if d.ifindex != p.epoch then none else d.rxSkbs[p.slot]?

/-- Paid cells remain in inventory until the actual free. Their historical
owner need not remain resident once no unpaid carrier/reservation charges it. -/
structure Inventory (cs : Ledger) (w : WGWorld) : Prop where
  distinct : (cs.map Carrier.packet).Nodup
  present : ∀ c ∈ cs, c.packet.epoch = c.owner.epoch ∧
    ∃ p, packetAt w c.packet = some p ∧ p.peer = c.owner.slot
  complete : ∀ d id p, w.dev = some d → d.rxSkbs[id]? = some p →
    ∃ c ∈ cs, c.packet = ⟨d.ifindex,id⟩

/-- Exact multiplicity of queue occurrences. The queue includes its peeked
head. Rings and worker locals are aliases, not further charged occurrences. -/
def QueueOwners (cs : Ledger) (w : WGWorld) : Prop :=
  ∀ d pid p id, w.dev = some d → d.peers[pid]? = some p →
    p.rxQueue.all.count id = (cs.filter fun c =>
      c.packet == ⟨d.ifindex,id⟩ && c.owner == ⟨d.ifindex,pid,p.internalId⟩ &&
      c.phase == .queued).length

def paid (c : Carrier) : Carrier := {c with phase := .paid}

def peerView (w : WGWorld) := (w.dev.map (·.ifindex), fun pid : PeerId =>
  (w.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.refcount,p.rxQueue))
def rxView (w : WGWorld) := (w.dev.map (·.ifindex), fun id : SkbId => w.dev.bind fun d => d.rxSkbs[id]?)

theorem protected_resident (hi : Protected cs loans w) (h : 0 < demand cs loans o) :
    ∃ p, resident w o = some p ∧ demand cs loans o ≤ p.refcount := by
  have hb := hi o
  cases hr : resident w o with
  | none => simp [balance,hr] at hb; omega
  | some p => exact ⟨p,rfl,by simpa [balance,hr] using hb⟩

@[simp] theorem charges_cons (c : Carrier) (cs : Ledger) (o : Owner) :
    charges (c :: cs) o = (if c.owner = o ∧ c.phase.charged = true then 1 else 0) + charges cs o := by
  simp [charges,List.filter_cons]
  split <;> simp_all [Nat.add_comm]

@[simp] theorem charges_paid (c : Carrier) (cs : Ledger) (o : Owner) :
    charges (paid c :: cs) o = charges cs o := by simp [paid,Phase.charged]

/-- One selected carrier supplies its own payment. Any remaining charge to
that owner forces a nonfinal put; this is derived arithmetic, not retention. -/
theorem selected_credit (hi : Protected (c :: cs) loans w) (hc : c.phase = .selected) :
    ∃ p, resident w c.owner = some p ∧
      1 + demand cs loans c.owner ≤ p.refcount := by
  have he : demand (c :: cs) loans c.owner = 1 + demand cs loans c.owner := by
    simp [demand,hc,Phase.charged,Nat.add_assoc]
  obtain ⟨p,hp,hb⟩ := protected_resident hi (o := c.owner) (by rw [he]; omega)
  exact ⟨p,hp,by simpa only [he] using hb⟩

theorem selected_nonfinal (hi : Protected (c :: cs) loans w) (hc : c.phase = .selected)
    (hr : 0 < demand cs loans c.owner) :
    ∃ p, resident w c.owner = some p ∧ 1 < p.refcount := by
  obtain ⟨p,hp,hb⟩ := selected_credit hi hc
  exact ⟨p,hp,by omega⟩

theorem resident_at (hd : w.dev = some d) (hp : d.peers[pid]? = some p) :
    resident w ⟨d.ifindex,pid,p.internalId⟩ = some p := by simp [resident,hd,hp]

theorem resident_fields (hr : resident w o = some p) :
    ∃ d, w.dev = some d ∧ d.ifindex = o.epoch ∧
      d.peers[o.slot]? = some p ∧ p.internalId = o.stamp := by
  cases hd : w.dev with
  | none => simp [resident,hd] at hr
  | some d =>
    by_cases he : d.ifindex = o.epoch
    · cases hp : d.peers[o.slot]? with
      | none => simp [resident,hd,he,hp] at hr
      | some q =>
        by_cases hs : q.internalId = o.stamp
        · simp [resident,hd,he,hp,hs] at hr
          subst q; exact ⟨d,rfl,he,hp,hs⟩
        · simp [resident,hd,he,hp,hs] at hr
    · simp [resident,hd,he] at hr

/-- Concrete nonfinal original payment changes only the current count. -/
theorem peerPut_nonfinal_spec (pid : PeerId) (initial : WGStoreView) (d : Device) (p : Peer)
    (hd : initial.dev = some d) (hp : d.peers[pid]? = some p) (hc : 1 < p.refcount) :
    ⦃fun w => ⌜wgStoreView w = initial⌝⦄ peerPut (some pid)
    ⦃⇓? _ w => ⌜wgStoreView w = {initial with dev := some ({d with peers := d.peers.insert pid {p with refcount := p.refcount - 1}})}⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hw hr
  have hd' : w.dev = some d := (congrArg WGStoreView.dev hw).trans hd
  have positive : 0 < p.refcount := by omega
  have nonzero : p.refcount ≠ 0 := by omega
  have nonfinal : p.refcount ≠ 1 := by omega
  simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
    refcountDecAndTest, branch, branchCmp, CounterWindow.branch_run,
    CounterWindow.branchCmp_run, hd', hp, positive, nonzero, nonfinal,
    StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
    CounterWindow.except_ok_bind, CounterWindow.except_pure] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  simpa only [wgStoreView] using congrArg
    (fun k : WGStoreView => {k with dev := some {d with peers := d.peers.insert pid {p with refcount := p.refcount - 1}}}) hw

/-- Source-acquired positivity, with the exact peer update retained. -/
theorem peerGet_loan (pid : PeerId) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((peerGet pid).run w).run ambient = .ok (((),v),ambient')) :
    PeerBorrow.Borrowed (wgStoreView w) (some pid) (wgStoreView v) :=
  (hoare_iff_run_ambient _ _ _).mp (PeerBorrow.strict_acquire_spec pid (wgStoreView w))
    w ambient () v ambient' rfl hr

end Leanux.Proofs.WG.Queues.RxCredits
