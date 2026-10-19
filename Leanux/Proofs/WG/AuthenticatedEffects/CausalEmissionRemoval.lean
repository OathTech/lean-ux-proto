import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionSend
import Leanux.Proofs.WG.HandshakeSecurity.EmissionLifecycle

/-! Removal and direct drains use the actual observed flushed-send callback.
Only the separately proved native clearing/deletion leaves are send-free. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Configuration TransmitSecurity.Driver HandshakeSecurity HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

macro "emission_removal_step" : tactic => `(tactic| first
  | (emission_native_head runFlushedClearWork; exact state_native _ (EmissionClearing.clear_work _))
  | (emission_native_head keypairsClear; exact state_native _ (EmissionClearing.keypairs _))
  | (emission_native_head delTimer; exact state_native _ (EmissionFrames.delete _ _))
  | (emission_native_head peerMakeDead; exact state_native _ (EmissionConfiguration.make_dead _))
  | (emission_native_head free; exact state_native _ EmissionAllowedIps.free)
  | (emission_head liftWGPrefix
     apply state_native
     try simp only [peekUnit,resolveUnit,getAmbient,WG.andM]
     sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec,peerPut_sent_spec,EmissionFrames.keypair_put_spec])
  | (emission_head ForIn.forIn; rw [Std.Legacy.Range.forIn_eq_forIn_range']; apply state_forIn)
  | emission_step)

theorem send_drain (upTo : Option PeerId) : StateSafe (sendDrainObserved hooks upTo) := by
  unfold sendDrainObserved drainWith
  repeat' first
    | (emission_head Hooks.flushedSend; exact flushed_send _)
    | emission_removal_step
  all_goals
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b hi run
    cases run

theorem remove_after (pid : PeerId) : StateSafe (afterDeadWith liftWGPrefix (sendDrainObserved hooks) pid) := by
  unfold afterDeadWith timersStopWith
  repeat' first
    | (emission_head sendDrainObserved; exact send_drain _)
    | emission_removal_step

theorem remove (peer : Option PeerId) : StateSafe (removeObserved hooks peer) := by
  unfold removeObserved removeWith peerRemoveWith
  repeat' first
    | (emission_head afterDeadWith; exact remove_after _)
    | emission_removal_step
  all_goals simp_all only [Option.some.injEq]
  all_goals first | exact remove_after _ | contradiction

theorem remove_all : StateSafe (removeAllObserved hooks) := by
  unfold removeAllObserved removeAllWith peerRemoveAllWith
  repeat' first
    | (emission_head afterDeadWith; exact remove_after _)
    | emission_removal_step
  all_goals exact state_native _ EmissionAllowedIps.free

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
