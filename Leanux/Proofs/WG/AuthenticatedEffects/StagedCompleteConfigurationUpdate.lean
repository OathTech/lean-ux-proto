import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConfigurationTail
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationUpdate

/-! The acquired-peer configuration update retains paired packet accounting across
its actual removal, metadata, endpoint, routing and guarded-send continuations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConfigurationUpdate
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity CompletePassive Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
variable (staging : ∀ pid, Checked debts locals Safe (stagingObserved hooks pid))
variable (keepalive : ∀ pid, Checked debts locals Safe (keepaliveObserved hooks pid))
variable (removed : ∀ peer, Checked debts locals Safe (removeObserved hooks peer))

include accountSafe staging keepalive removed

theorem update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    Checked debts locals Safe (configUpdate hooks attrs peer flags psk pid) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (entry_plain_update_head
       simpa only [Queued.lift_bind] using CompletePassive.native Safe accountSafe
         (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []})
         (Queued.update pid (fun p => {p with presharedKey := psk.getD []}) (fun _ => ⟨rfl,rfl,rfl⟩)))
    | (maintenance_head configOut; exact CompleteConfigurationTail.out Safe accountSafe _ _ _)
    | (maintenance_head configTail; exact CompleteConfigurationTail.tail Safe accountSafe staging keepalive _ _ _)
    | (maintenance_head removeObserved; exact removed _)
    | (maintenance_lift_action_head WG.andM
       apply CompletePassive.native Safe accountSafe
       intro initial
       change Preserves (fun w => StagedEntry.view w = initial) _
       unfold WG.andM
       simp only [branch]
       repeat' entry_control_step initial)
    | complete_config_tail_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConfigurationUpdate
