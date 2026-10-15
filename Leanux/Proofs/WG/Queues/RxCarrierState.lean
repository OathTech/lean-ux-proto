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

def resident (w : World) (o : Owner) : Option Peer := do
  let d ← w.k.wg
  if d.ifindex != o.epoch then none else do
    let p ← d.peers[o.slot]?
    if p.internalId != o.stamp then none else some p

def balance (w : World) (o : Owner) : Nat := ((resident w o).map (·.refcount)).getD 0

def charges (cs : Ledger) (o : Owner) : Nat :=
  (cs.filter fun c => c.owner == o && c.phase.charged).length

def demand (cs : Ledger) (loans : Reservations) (o : Owner) := charges cs o + loans.count o

def Protected (cs : Ledger) (loans : Reservations) (w : World) : Prop :=
  ∀ o, demand cs loans o ≤ balance w o

def packetAt (w : World) (p : Packet) : Option RxPacket := do
  let d ← w.k.wg
  if d.ifindex != p.epoch then none else d.rxSkbs[p.slot]?

/-- Paid cells remain in inventory until the actual free. Their historical
owner need not remain resident once no unpaid carrier/reservation charges it. -/
structure Inventory (cs : Ledger) (w : World) : Prop where
  distinct : (cs.map Carrier.packet).Nodup
  present : ∀ c ∈ cs, c.packet.epoch = c.owner.epoch ∧
    ∃ p, packetAt w c.packet = some p ∧ p.peer = c.owner.slot
  complete : ∀ d id p, w.k.wg = some d → d.rxSkbs[id]? = some p →
    ∃ c ∈ cs, c.packet = ⟨d.ifindex,id⟩

/-- Exact multiplicity of queue occurrences. The queue includes its peeked
head. Rings and worker locals are aliases, not further charged occurrences. -/
def QueueOwners (cs : Ledger) (w : World) : Prop :=
  ∀ d pid p id, w.k.wg = some d → d.peers[pid]? = some p →
    p.rxQueue.all.count id = (cs.filter fun c =>
      c.packet == ⟨d.ifindex,id⟩ && c.owner == ⟨d.ifindex,pid,p.internalId⟩ &&
      c.phase == .queued).length

def paid (c : Carrier) : Carrier := {c with phase := .paid}

def peerView (w : World) := (w.k.wg.map (·.ifindex), fun pid : PeerId =>
  (w.k.wg.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.refcount,p.rxQueue))
def rxView (w : World) := (w.k.wg.map (·.ifindex), fun id : SkbId => w.k.wg.bind fun d => d.rxSkbs[id]?)

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

theorem resident_at (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p) :
    resident w ⟨d.ifindex,pid,p.internalId⟩ = some p := by simp [resident,hd,hp]

theorem resident_fields (hr : resident w o = some p) :
    ∃ d, w.k.wg = some d ∧ d.ifindex = o.epoch ∧
      d.peers[o.slot]? = some p ∧ p.internalId = o.stamp := by
  cases hd : w.k.wg with
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
theorem peerPut_nonfinal_spec (pid : PeerId) (initial : Kernel) (d : Device) (p : Peer)
    (hd : initial.wg = some d) (hp : d.peers[pid]? = some p) (hc : 1 < p.refcount) :
    ⦃fun w => ⌜w.k = initial⌝⦄ peerPut (some pid)
    ⦃⇓? _ w => ⌜w.k = {initial with wg := some ({d with peers := d.peers.insert pid {p with refcount := p.refcount - 1}})}⌝⦄ := by
  have hg := PeerBorrow.getPeer_known initial d pid p hd hp
  simp only [peerPut]
  mvcgen [hg,requireNotPending,setPeer,modifyDev,modifyK,refcountDecAndTest,
    branch,branchCmp,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals omega

/-- Source-acquired positivity, with the exact peer update retained. -/
theorem peerGet_loan (pid : PeerId) (w v : World)
    (hr : (peerGet pid).run w = .ok ((),v)) : PeerBorrow.Borrowed w.k (some pid) v.k :=
  (hoare_iff_triple _ _ _).mpr (PeerBorrow.strict_acquire_spec pid w.k) w () v rfl hr

end Leanux.Proofs.WG.Queues.RxCredits
