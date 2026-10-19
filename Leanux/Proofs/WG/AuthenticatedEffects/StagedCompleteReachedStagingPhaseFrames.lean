import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseContracts

/-! Concrete frames for selected ownership. The original selected ledger,
ordered cohort and native take anchor remain unchanged through these leaves.
Nonce receipts have their own complete selected-state transport. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity CausalJournal Staged.Obligations Staging.Points
set_option maxHeartbeats 600000

theorem preserved {action : WGPrefix Event α}
    (rule : StatePrefixPreserves P Safe action) (before : P h w a)
    (run : runWGPrefix action w a h=(.ok ((value,u),b),middle)) : P middle u b := by
  obtain ⟨_,_,_,post⟩:=rule w a h before
  change runPrefix (action.run w) a h=_ at run
  rw [run] at post
  exact post

theorem selected_world (token : Native α) (same : SameView id token.action)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position) (.native token) w a h := by
  refine ⟨before,fun value u b middle run=>?_⟩
  exact preserved (CompleteSelected.world (fun _=>id) _ same) before run

theorem selected_ambient (token : Native α) (action : AmbientM α)
    (same : token.action=(monadLift action : WG.M α))
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position) (.native token) w a h := by
  refine ⟨before,fun value u b middle run=>?_⟩
  rw [same] at run
  exact preserved (CompleteSelected.ambient (fun _=>id) action) before run

theorem selected_key (kid : KeypairId)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position) (.native (.key kid)) w a h :=
  ⟨before,fun _ _ _ _ run=>preserved (CompleteSelected.read_key (fun _=>id) kid) before run⟩

theorem selected_reserve (kid : KeypairId)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position) (.child (.reserve kid)) w a h :=
  ⟨before,fun _ _ _ _ run=>preserved (CompleteSelected.reserve (fun _=>id) kid) before run⟩

theorem selected_write_key (kid : KeypairId) (key : Keypair)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position) (.native (.setKey kid key)) w a h := by
  refine ⟨before,fun value u b middle run=>?_⟩
  have rule : StatePrefixPreserves (CompleteSelected.Ready ledger debts locals generation pid peer position)
      (CompleteSelected.Active ledger debts generation pid peer position) (liftWGPrefix (setKeypair kid key)) := CompleteSelected.decorate
    (ReadyCarrier.decorate
      (SoundHeld.decorate (fun _=>id) (HeldFrontier.held_write_key (fun _=>id) kid key))
      (erasesStatePrefix_lift _) (NativeReady.write_key kid key))
    (Driver.History.state_lift _) (fun _=>id)
  exact preserved rule before run

theorem native_get_peer (pid : PeerId) : SameView id (getPeer pid) := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b saved run
  obtain ⟨rfl,_,_⟩:=Origins.getPeer_return pid w v value a b run
  exact saved

theorem native_ecn (packet : Packet) : SameView id (ipTunnelEcnEncap packet) :=
  ipTunnelEcnEncap_sameWGWorld packet

theorem native_owner (kid : KeypairId) : SameView id (IndexOwner.peerDeref (.keypair kid)) :=
  fun initial=>indexOwner_peerDeref_preserves _ (fun w=>w=initial)

theorem native_inc_not_zero (count : Nat) : SameView id (refcountIncNotZero count : WG.M Bool) := by
  intro initial
  change Preserves (fun w=>w=initial) _
  unfold refcountIncNotZero
  simp only [branch,branchCmp,unsupported]
  repeat' first
    | (rx_retention_head MonadLiftT.monadLift; exact hoare_liftAmbient _ _)
    | (rx_retention_head MonadLift.monadLift; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
