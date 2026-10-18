import Leanux.Proofs.WG.RetirementSecurity.Payments
import Leanux.Proofs.WG.RetirementSecurity.Clear

/-! The original clear operation pays the references in the peer's three
actual publication slots. Optional stamped loans align with those slots;
their multiplicities remain significant when two slots alias one allocation.
The remaining credits still require alignment with other holders. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

def peerAt (w : WGWorld) (pid : PeerId) : Option Peer :=
  w.dev.bind fun d => d.peers[pid]?

inductive KeySlot where
  | next | previous | current

def KeySlot.get : KeySlot → Peer → Option KeypairId
  | .next, p => p.keypairNext
  | .previous, p => p.keypairPrevious
  | .current, p => p.keypairCurrent

def KeySlot.clear : KeySlot → Peer → Peer
  | .next, p => {p with keypairNext := none}
  | .previous, p => {p with keypairPrevious := none}
  | .current, p => {p with keypairCurrent := none}

structure SlotLoans where
  next : Option Credits.Allocation
  previous : Option Credits.Allocation
  current : Option Credits.Allocation

def SlotLoans.credits (loans : SlotLoans) : Credits.Ledger :=
  loans.next.toList ++ loans.previous.toList ++ loans.current.toList

def SlotLoans.Aligned (loans : SlotLoans) (p : Peer) : Prop :=
  loans.next.map (·.slot) = p.keypairNext ∧
  loans.previous.map (·.slot) = p.keypairPrevious ∧
  loans.current.map (·.slot) = p.keypairCurrent

def PeerAccount (pid : PeerId) (p : Peer) (credits : Credits.Ledger)
    (w : WGWorld) : Prop :=
  peerAt w pid = some p ∧ Credits.Exact credits w

theorem read_peer_account (pid : PeerId) (p : Peer) (credits : Credits.Ledger) :
    Hoare (getPeer pid) (PeerAccount pid p credits)
      (fun read w => read = p ∧ PeerAccount pid p credits w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a read v b hi run
  cases device : w.dev with
  | none => simp [PeerAccount,peerAt,device] at hi
  | some d =>
    have stored : d.peers[pid]? = some p := by simpa [peerAt,device] using hi.1
    have actual : ((getPeer pid).run w).run a = .ok ((p,w),a) := by
      simp [getPeer,getDev,device,stored]
    rw [actual] at run
    cases run
    exact ⟨rfl,hi⟩

theorem write_peer_account (pid : PeerId) (p q : Peer) (credits : Credits.Ledger) :
    Hoare (setPeer pid q) (PeerAccount pid p credits)
      (fun _ => PeerAccount pid q credits) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases run
  cases device : w.dev with
  | none => simp [PeerAccount,peerAt,device] at hi
  | some d =>
    constructor
    · simp [peerAt,device]
    · intro allocation
      simpa [Credits.balance,keyAt,device] using hi.2 allocation

theorem put_peer_account (pid : PeerId) (p : Peer) (loan : Option Credits.Allocation)
    (remaining : Credits.Ledger) (now : Bool) :
    Hoare (keypairPut (loan.map (·.slot)) now)
      (PeerAccount pid p (loan.toList ++ remaining))
      (fun _ => PeerAccount pid p remaining) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  cases loan with
  | none =>
    simp [keypairPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact hi
  | some allocation =>
    change ((keypairPut (some allocation.slot) now).run w).run a = .ok (((),v),b) at run
    have peers := congrArg (fun maps => maps.bind fun peers => peers[pid]?)
      (put_peers (some allocation.slot) now w v a b run)
    simp only [peersAt,Option.bind_map,Function.comp_def] at peers
    have account : Credits.Exact (allocation :: remaining) w := hi.2
    exact ⟨peers.trans hi.1,account.put now a b run⟩

def updateSlot (pid : PeerId) (slot : KeySlot) : WG.M Unit := do
  let p ← getPeer pid
  setPeer pid (slot.clear p)

/-- A source abbreviation retaining both native peer getters and the put. -/
def clearSlot (pid : PeerId) (slot : KeySlot) : WG.M Unit := do
  let old := slot.get (← getPeer pid)
  updateSlot pid slot
  keypairPut old true

theorem clearSlot_account (pid : PeerId) (slot : KeySlot) (p : Peer)
    (loan : Option Credits.Allocation) (remaining : Credits.Ledger)
    (aligned : loan.map (·.slot) = slot.get p) :
    Hoare (clearSlot pid slot) (PeerAccount pid p (loan.toList ++ remaining))
      (fun _ => PeerAccount pid (slot.clear p) remaining) := by
  unfold clearSlot
  apply hoare_bind _ _ (read_peer_account pid p _)
  intro read
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨equal,hi⟩ := hi
  subst read
  have rest : Hoare (do
      let q ← getPeer pid
      setPeer pid (slot.clear q)
      keypairPut (slot.get p) true)
      (PeerAccount pid p (loan.toList ++ remaining))
      (fun _ => PeerAccount pid (slot.clear p) remaining) := by
    apply hoare_bind _ _ (read_peer_account pid p _)
    intro q
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u c result z e hq execute
    obtain ⟨equal,hq⟩ := hq
    subst q
    have write := write_peer_account pid p (slot.clear p) (loan.toList ++ remaining)
    have put := put_peer_account pid (slot.clear p) loan remaining true
    rw [aligned] at put
    exact (hoare_iff_run_ambient _ _ _).mp
      (hoare_bind _ _ write (fun _ => put)) u c result z e hq execute
  simp only [updateSlot,bind_assoc] at run
  exact (hoare_iff_run_ambient _ _ _).mp rest w a result v b hi run

theorem clear_source (pid : PeerId) : keypairsClear pid = (do
    clearSlot pid .next
    clearSlot pid .previous
    clearSlot pid .current) := by
  unfold keypairsClear
  change (do
    let p ← getPeer pid
    updateSlot pid .next
    keypairPut p.keypairNext true
    let p ← getPeer pid
    updateSlot pid .previous
    keypairPut p.keypairPrevious true
    let p ← getPeer pid
    updateSlot pid .current
    keypairPut p.keypairCurrent true) = _
  simp only [clearSlot,KeySlot.get,bind_assoc]

/-- Clearing the actual slots pays exactly those occurrences, retaining
the funding of all references outside the three slots. -/
theorem clear_slot_account (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (remaining : Credits.Ledger) (aligned : loans.Aligned p) :
    Hoare (keypairsClear pid) (PeerAccount pid p (loans.credits ++ remaining))
      (fun _ => PeerAccount pid
        {p with keypairNext := none, keypairPrevious := none, keypairCurrent := none}
        remaining) := by
  rw [clear_source]
  simp only [SlotLoans.credits,List.append_assoc]
  apply hoare_bind _ _ (clearSlot_account pid .next p loans.next
    (loans.previous.toList ++ (loans.current.toList ++ remaining)) aligned.1)
  intro _
  apply hoare_bind _ _ (clearSlot_account pid .previous (KeySlot.next.clear p) loans.previous
    (loans.current.toList ++ remaining) aligned.2.1)
  intro _
  exact clearSlot_account pid .current (KeySlot.previous.clear (KeySlot.next.clear p)) loans.current
    remaining aligned.2.2

end Leanux.Proofs.WG.RetirementSecurity
