import Leanux.Proofs.WG.HandshakeSecurity.ResponderStagingSource
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDecoration

/-! The staged queue leaves the resident peer before current-key borrowing.
This exact cut retains caller-local packets if the later borrow stops; the old
completed selection receipt remains an outer observer of the same execution. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Take
open Leanux Leanux.WG Leanux.Proofs.Logged

def takePrefix (pid : PeerId) : WG.M (Option Peer) := do
  let p ← getPeer pid
  if ← branch .stagedEmpty p.staged.isEmpty then return none
  setPeer pid {p with staged := []}
  return some p

def borrow : Option Peer → WG.M (Option (Peer × Option KeypairId))
  | none => pure none
  | some p => do
    let key ← keypairGet p.keypairCurrent
    return some (p,key)

theorem selection_factor (pid : PeerId) :
    Responder.selectionPrefix pid = takePrefix pid >>= borrow := by
  unfold Responder.selectionPrefix takePrefix
  simp only [bind_assoc,Queues.RxCredits.bind_if_source,pure_bind,borrow]

structure Receipt where
  pid : PeerId
  run : WGRunWitness (Option Peer)

def Receipt.Valid (r : Receipt) : Prop := r.run.Valid (takePrefix r.pid)

def observed (record : Receipt → E) (pid : PeerId) :
    WGPrefix E (Option (Peer × Option KeypairId)) := do
  let taken ← receiptWGObserved (liftWGPrefix (takePrefix pid)) (fun run => record ⟨pid,run⟩)
  liftWGPrefix (borrow taken)

def selection (record : Receipt → E)
    (selected : PeerId → WGRunWitness (Option (Peer × Option KeypairId)) → E)
    (pid : PeerId) : WGPrefix E (Option (Peer × Option KeypairId)) :=
  receiptWGObserved (observed record pid) (selected pid)

theorem observed_erases (record : Receipt → E) (pid : PeerId) :
    ErasesStatePrefix (observed record pid) (Responder.selectionPrefix pid) := by
  rw [selection_factor]
  exact erasesStatePrefix_bind
    (receiptWGObserved_erases (erasesStatePrefix_lift _) _) (fun _ => erasesStatePrefix_lift _)

theorem observed_projects (record : Receipt → E) (ρ : E → Option F)
    (quiet : ∀ r, ρ (record r) = none) (pid : PeerId) :
    StateProjectsPrefix ρ id (observed record pid) (liftWGPrefix (Responder.selectionPrefix pid)) := by
  rw [selection_factor]
  have factor : (liftWGPrefix (takePrefix pid >>= borrow) : WGPrefix F _) =
      (do let taken ← liftWGPrefix (takePrefix pid); liftWGPrefix (borrow taken)) := by
    funext w a h
    change runWGPrefix (liftWGPrefix (_ >>= _)) w a h = runWGPrefix (_ >>= _) w a h
    simp only [runWGPrefix,runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift,StateT.run_bind]
    cases ((takePrefix pid).run w).run a with
    | error _ => rfl
    | ok out => rcases out with ⟨⟨x,v⟩,b⟩; rfl
  rw [factor]
  exact StateProjectsPrefix.bind ρ id id
    (Exchange.receipt_ignored ρ _ _ _
      (Exchange.quiet_native_projection ρ _ _ (erasesStatePrefix_lift _) (fun _ _ _ => rfl))
      (fun _ => quiet _))
    (fun _ => Exchange.quiet_native_projection ρ _ _ (erasesStatePrefix_lift _) (fun _ _ _ => rfl))

theorem selection_projects (record : Receipt → E) (ρ : E → Option F)
    (quiet : ∀ r, ρ (record r) = none)
    (selected : PeerId → WGRunWitness (Option (Peer × Option KeypairId)) → E)
    (target : PeerId → WGRunWitness (Option (Peer × Option KeypairId)) → F)
    (matching : ∀ pid r, ρ (selected pid r) = some (target pid r)) (pid : PeerId) :
    StateProjectsPrefix ρ id (selection record selected pid)
      (receiptWGObserved (liftWGPrefix (Responder.selectionPrefix pid)) (target pid)) :=
  Exchange.receipt_projects ρ _ _ _ _ (observed_projects record ρ quiet pid) (matching pid)

/-- A completed take is recorded before key borrowing is entered. This
identity also covers a later Stop in that native borrow. -/
theorem observed_after_take (record : Receipt → E) (pid : PeerId)
    (w v : WGWorld) (a b : Ambient) (h : List E) (taken : Option Peer)
    (run : ((takePrefix pid).run w).run a = .ok ((taken,v),b)) :
    runWGPrefix (observed record pid) w a h =
      runWGPrefix (liftWGPrefix (borrow taken)) v b
        (h ++ [record ⟨pid,⟨taken,w,v,a,b⟩⟩]) := by
  unfold observed
  rw [runWGPrefix,runStatePrefix_bind]
  have captured := runWGPrefix_receiptWGObserved (liftWGPrefix (takePrefix pid))
    (fun r => record ⟨pid,r⟩) w a h
  rw [runWGPrefix_lift,run] at captured
  change runStatePrefix _ w a h = _ at captured
  rw [captured]
  rfl

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Take
