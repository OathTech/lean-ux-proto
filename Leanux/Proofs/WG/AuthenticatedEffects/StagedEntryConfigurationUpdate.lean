import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationTail

/-! The acquired-peer configuration update retains packet accounting across
its actual removal, metadata, endpoint, routing and guarded-send continuations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationUpdate
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity SourcePassive Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open Lean Meta Elab Tactic in
elab "entry_plain_update_head" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do throwError "not an observer contract"
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not an observer bind"
  let parts := action.getAppArgs
  let head := parts[parts.size - 2]!.consumeMData
  unless head.isAppOf ``liftWGPrefix do throwError "not a native lift"
  unless head.getAppArgs.back!.consumeMData.isAppOf ``getPeer do throwError "not a peer read"
  let .lam _ _ body _ := parts.back!.consumeMData | throwError "not an explicit continuation"
  unless body.consumeMData.isAppOf ``liftWGPrefix do throwError "not a native write"
  unless body.consumeMData.getAppArgs.back!.consumeMData.isAppOf ``setPeer do throwError "not a peer write"

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
variable (staging : ∀ pid, Checked debts locals Safe (stagingObserved hooks pid))
variable (keepalive : ∀ pid, Checked debts locals Safe (keepaliveObserved hooks pid))
variable (removed : ∀ peer, Checked debts locals Safe (removeObserved hooks peer))

include entrySafe staging keepalive removed

theorem update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    Checked debts locals Safe (configUpdate hooks attrs peer flags psk pid) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (entry_plain_update_head
       exact fixed Safe entrySafe (fun _ => Passive.update pid
         (fun p => {p with presharedKey := psk.getD []}) (fun _ => ⟨rfl,rfl,rfl⟩)))
    | (maintenance_head configOut; exact ConfigurationTail.out Safe entrySafe _ _ _)
    | (maintenance_head configTail; exact ConfigurationTail.tail Safe entrySafe staging keepalive _ _ _)
    | (maintenance_head removeObserved; exact removed _)
    | (maintenance_lift_action_head WG.andM
       apply SourcePassive.native Safe entrySafe
       intro initial
       change Preserves (fun w => StagedEntry.view w = initial) _
       unfold WG.andM
       simp only [branch]
       repeat' entry_control_step initial)
    | entry_config_tail_step Safe using entrySafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationUpdate
