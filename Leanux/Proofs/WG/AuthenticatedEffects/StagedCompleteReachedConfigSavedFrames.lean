import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigSavedSource

/-! The saved-peer frame is established by the actual read. Allocation uses
the same native execution as campaign 1's existing configuration observer. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigSaved
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal RetirementSecurity

theorem observer_erases (pid : PeerId) (running : Bool) (interval : Nat) :
    ErasesStatePrefix (observer pid running interval) (native pid running interval) := by
  unfold observer native
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro send
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _=>erasesStatePrefix_pure send)

theorem lifetime_erases (pid : PeerId) (running : Bool) (interval : Nat) :
    ErasesStatePrefix (configureKeepaliveValuePrefix pid running interval) (native pid running interval) := by
  unfold configureKeepaliveValuePrefix native decision
  apply erasesStatePrefix_bind (getPeerMixed_erases _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro send
  exact erasesStatePrefix_bind (setPeerMixed_erases _ _) (fun _=>erasesStatePrefix_pure send)

theorem checked (pid : PeerId) (running : Bool) (interval : Nat) :
    CompleteProduct.Checked (action pid running interval) := by
  apply CompleteProduct.state
  apply CompleteProduct.pair (erases:=observer_erases pid running interval)
  · unfold observer
    apply StatePrefixEnsures.bind (CompleteSaved.read CompleteProduct.Safe CompleteProduct.account_safe pid)
    intro p
    apply StatePrefixEnsures.bind (CompleteSaved.store CompleteProduct.Safe CompleteProduct.account_safe pid p _
      (Staged.Origins.Native.keepalive_decision p interval running))
    intro send
    apply StatePrefixEnsures.bind (CompleteSaved.write CompleteProduct.Safe CompleteProduct.account_safe pid p
      (fun q=>{q with persistentKeepaliveInterval:=interval}) (fun _=>⟨rfl,rfl,rfl⟩))
    intro _
    exact CompletePassive.pure_checked CompleteProduct.Safe CompleteProduct.account_safe send
  · exact AllocatedFrames.observed (lifetime_erases pid running interval)
      (AmbientContracts.drop (configureKeepaliveValuePrefix_spec allocationAmbient (fun _=>True) pid running interval))

theorem read_checked (pid : PeerId) : CompleteProduct.Checked (read pid) :=
  CompleteProduct.state (CompleteConfigurationReady.passive CompleteProduct.Safe CompleteProduct.account_safe
    _ (TimerFrames.store (CompleteProduct.peer_read_store pid)) (AllocatedFrames.read pid))

theorem decide_checked (p : Peer) (running : Bool) (interval : Nat) :
    CompleteProduct.Checked (decide p running interval) :=
  CompleteProduct.state (CompleteConfigurationReady.passive CompleteProduct.Safe CompleteProduct.account_safe
    _ (TimerFrames.store (Staged.Origins.Native.keepalive_decision p interval running))
    (AllocatedFrames.store (Staged.Origins.Native.keepalive_decision p interval running)))

/-- Security: the saved keepalive metadata write conserves the original
packet account; its read and decision cuts use that same actual entry. -/
theorem Point.normal (before : CompleteProduct.Carrier h w)
    (point : Point pid running interval w h u middle) : CompleteProduct.Carrier middle u := by
  cases point with
  | entry=>exact before
  | read got=>exact Xmit.normal (read_checked pid) before got
  | decided got guarded=>
      exact Xmit.normal (decide_checked _ running interval) (Xmit.normal (read_checked pid) before got) guarded
  | written got guarded stored=>
      rename_i prior p v later send x
      apply Xmit.normal (value:=send) (checked pid running interval) before
      simp only [source,runPrefix_bind,got,guarded,stored,runPrefix_pure]
  | returned performed=>exact Xmit.normal (checked pid running interval) before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigSaved
