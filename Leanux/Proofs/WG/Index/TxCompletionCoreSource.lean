import Leanux.Proofs.WG.Noise.SendSkbRulesSource
import Leanux.Proofs.WG.Index.TxSelectionFrames
import Leanux.Proofs.WG.Noise.DataCompletionRulesSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.CryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem socket_core {α : Type} (action : WG.M α) (pid : PeerId)
    (work : ∀ q v,⦃fun w => ⌜TimerDiscipline.sendWorkAt w pid=(q,v)⌝⦄ action
      ⦃⇓? _ w => ⌜TimerDiscipline.sendWorkAt w pid=(q,v)⌝⦄)
    (material : SameView Origins.view action) : Preserves Reached.Core action := by
  apply (ensures_iff _ _ _).mp
  apply TimerCore.sender_core action _ (sender_fields_of_sendWork_material action pid work material)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  have frame := (ensures_iff _ _ _).mpr
    (TimerDiscipline.send_frame_of_sendWork_native action pid work
      (TimerDiscipline.sendAt w pid).1 (TimerDiscipline.sendAt w pid).2)
    w a result v b rfl run
  exact tablesSafe_of_cursor w v (congrArg Prod.fst frame) pre

theorem sendSkb_core (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Preserves Reached.Core (sendSkbToPeer pid bytes ds) :=
  DataCompletionRules.sendSkb_preserves _ pid bytes ds
    (fun e exactRx => socket_core _ pid
      (TimerDiscipline.send4_sendWorkView pid e bytes ds exactRx)
      (Origins.Retaining.send4_material e (some pid) bytes ds exactRx))
    (fun e exactRx => socket_core _ pid
      (TimerDiscipline.send6_sendWorkView pid e bytes ds exactRx)
      (Origins.Retaining.send6_material e (some pid) bytes ds exactRx))
    (ConfigurationIndex.frame_core (ConfigurationIndex.modifyPeer_fields pid
      (fun p => {p with txBytes:=p.txBytes+bytes.length}) (fun _=>rfl)))

theorem guardedArm_core (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    Preserves Reached.Core (do if ← modPeerTimerGuard pid then armTimer pid timer delay caller) := by
  apply (ensures_iff _ _ _).mp
  apply TimerCore.sender_core
  · apply (ensures_iff _ _ _).mp
    refine ensures_bind _ _
      ((pinned_const _private.Leanux.Proofs.WG.Index.SendFrames.«0».Leanux.Proofs.WG.Index.timerGuard_tables_resident) pid) ?_
    intro allowed
    cases allowed with
    | false =>
      intro w a result v b pre run
      cases run
      exact pre.1
    | true =>
      exact (pinned_const _private.Leanux.Proofs.WG.Index.SendFrames.«0».Leanux.Proofs.WG.Index.armTimer_tables_resident)
        pid timer delay caller
  · intro initial
    exact (ensures_iff _ _ _).mp (sender_guardedArm pid timer delay caller initial)

theorem dataSent_core (pid : PeerId) : Preserves Reached.Core (timersDataSent pid) := by
  rw [TimerDiscipline.dataSent_source]
  unfold TimerDiscipline.dataSentPrefix
  simp only [bind_assoc]
  apply preserves_bind
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b pre run
    exact (getPeer_normal pid w v p a b run).1 ▸ pre
  · intro p
    apply preserves_bind (hoare_liftAmbient
      (AmbientM.branch .timersDataSentNotPending !(p.timerPending .newHandshake)) Reached.Core)
    intro ready
    cases ready with
    | false => exact preserves_pure ()
    | true =>
      unfold TimerDiscipline.jitteredArm
      exact preserves_bind ((callerJiffies_sameWGWorld .timerJiffiesDataSent).wp Reached.Core) (fun caller=>
        preserves_bind ((jitterBelowRekeyTimeout_sameWGWorld .newHandshakeJitter).wp Reached.Core) (fun jitter=>
          guardedArm_core pid .newHandshake (KEEPALIVE_TIMEOUT_TICKS+REKEY_TIMEOUT_TICKS+jitter) caller))

theorem completion_core (pid : PeerId) (item : List SkbId) :
    Preserves Reached.Core (createDataDone pid item) := by
  exact DataCompletionRules.preserves _ pid item
    ((ensures_iff _ _ _).mp (TimerCore.sender_core _ (traversal_tables pid) (sender_traversal pid)))
    ((ensures_iff _ _ _).mp (TimerCore.sender_core _ (delTimer_tables pid .sendKeepalive)
      (sender_delTimer pid .sendKeepalive)))
    (sendSkb_core pid) (dataSent_core pid)
    (TxReservation.keepKeyFresh_preserves _ pid ((ensures_iff _ _ _).mp (TimerCore.queued_core pid false)))

theorem completion_boundary (cs : Ledger) (loans : Reservations)
    (history : List SessionOrigin.Receipt) (pid : PeerId) (item : List SkbId)
    (w v : WGWorld) (a b : Ambient)
    (entry : DeviceBoundary.Entry cs loans w ∧ Reached.Core w)
    (current : CurrentLifecycle.Inv history w)
    (run : ((createDataDone pid item).run w).run a=.ok (((),v),b)) :
    DeviceBoundary.Entry cs loans v ∧ Reached.Core v := by
  obtain ⟨holders,funded,stable⟩ := entry.1.1
  obtain ⟨delta,handoff,_,post⟩ := TxReservation.createDataDone_handoff pid item
    ⟨funded.carriers,stable⟩ a b run
  have passive := (ProjectedAction.iff_run_ambient _ _ _).mp
    (createDataDone_passive pid item) w a () v b run
  have input : holders.Funded cs (loans++[]) w := by simpa only [List.append_nil] using funded
  have after : (holders.absorb delta).Funded cs loans v := by
    simpa only [List.append_nil] using input.handoff handoff post.1.keys passive
  have configured := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.complete_preserves) pid item history)
    w a () v b current run
  exact ⟨⟨⟨holders.absorb delta,after,post.2⟩,
      BaseCoherence.transport entry.1.2.1
        ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.createDataDone_view pid item) w a () v b run),
      configured.1⟩,
    (hoare_iff_run_ambient _ _ _).mp (completion_core pid item) w a () v b entry.2 run⟩

end Leanux.Proofs.WG.Index.CryptCore
