import Leanux.Proofs.WG.RetirementSecurity.SlotPayments

/-! A concrete boundary projection of native key-reference holders. Three
peer slots each carry one occurrence, each RX queue entry carries one, and
each TX queue batch carries one through its head. Device-ring aliases and
dispatch notifications add none. Missing heads, packets or allocations reject
the projection rather than silently dropping an unaccounted holder.

Source-local references between acquisition and publication, or between
queue removal and payment, remain explicit temporary occurrences. Deriving
their complete transport through initialized executions is still required. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

inductive KeyHolder where
  | peerSlot (peer : PeerId) (slot : KeySlot)
  | receive (peer : PeerId) (packet : SkbId)
  | transmit (peer : PeerId) (batch : List SkbId)

structure KeyLoan where
  holder : KeyHolder
  allocation : Credits.Allocation

def nameLoan (w : WGWorld) (holder : KeyHolder) (key : KeypairId) : Option KeyLoan := do
  let resident ← keyAt w key
  return ⟨holder,⟨key,resident.internalId⟩⟩

def peerLoans (w : WGWorld) (pid : PeerId) (p : Peer) : Option (List KeyLoan) := do
  let next ← p.keypairNext.toList.mapM (nameLoan w (.peerSlot pid .next))
  let previous ← p.keypairPrevious.toList.mapM (nameLoan w (.peerSlot pid .previous))
  let current ← p.keypairCurrent.toList.mapM (nameLoan w (.peerSlot pid .current))
  let tx ← p.txQueue.all.mapM fun batch => do
    let head ← batch.head?
    let packet ← w.dev.bind fun d => d.txSkbs[head]?
    nameLoan w (.transmit pid batch) packet.keypair
  let rx ← p.rxQueue.all.mapM fun id => do
    let packet ← w.dev.bind fun d => d.rxSkbs[id]?
    nameLoan w (.receive pid id) packet.keypair
  return next ++ previous ++ current ++ tx ++ rx

def durableLoans (w : WGWorld) : Option (List KeyLoan) := do
  match w.dev with
  | none => return []
  | some d =>
    let peers ← d.peers.toList.mapM fun (pid,p) => peerLoans w pid p
    return peers.flatten

/-- The durable occurrences are fixed by the native state. Only explicitly
in-flight source locals are supplied separately. This predicate is not itself
a proof that callers generate and pay those locals correctly. -/
def HolderAccount (temporary : Credits.Ledger) (w : WGWorld) : Prop :=
  ∃ durable, durableLoans w = some durable ∧
    Credits.Exact (durable.map (·.allocation) ++ temporary) w

theorem nameLoan_resident (found : nameLoan w holder key = some loan) :
    loan.holder = holder ∧ loan.allocation.slot = key ∧
      ∃ resident, keyAt w key = some resident ∧
        loan.allocation.stamp = resident.internalId := by
  unfold nameLoan at found
  cases cell : keyAt w key with
  | none => simp [cell] at found
  | some resident =>
    simp [cell] at found
    subst loan
    exact ⟨rfl,rfl,resident,rfl,rfl⟩

theorem initial_holder_account (net bare : Bool) :
    HolderAccount [] (Runner.initialWG net bare) := by
  refine ⟨[],?_,?_⟩
  · cases net <;> cases bare <;> simp [durableLoans,Runner.initialWG] <;> rfl
  · exact Credits.initial net bare

end Leanux.Proofs.WG.RetirementSecurity
