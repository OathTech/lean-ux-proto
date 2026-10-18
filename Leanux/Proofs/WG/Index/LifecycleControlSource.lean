import Leanux.Proofs.WG.Index.LifecycleMaintenanceSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.LifecycleIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits Queues.RxCredits.DurableHolders
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open ConfigurationIndex

theorem native_lift {α : Type} (P : WGWorld → Prop) (action : WG.M α)
    (keeps : Preserves P action) :
    StatePrefixPreserves (fun (_ : List Unit) w (_ : Ambient) => P w)
      (fun _ => True) (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ _ => trivial)
    (fun _ w a x v b pre run => (hoare_iff_run_ambient _ _ _).mp keeps w a x v b pre run)

theorem native_erased {α : Type} (P : WGWorld → Prop) (observed : WGPrefix Unit α)
    (action : WG.M α) (erases : ErasesStatePrefix observed action)
    (keeps : StatePrefixPreserves (fun _ w _ => P w) (fun _ => True) observed) :
    Preserves P action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  obtain ⟨suffix,_,_,post⟩ := keeps w a [] pre
  have result_eq := (erases w a []).trans run
  change (runPrefix (observed.run w) a []).1 = .ok ((result,v),b) at result_eq
  simp only [result_eq] at post
  exact post

def stopPeerPlain (pid : PeerId) : WGPrefix Unit Unit :=
  DriverTags.Control.stopPeerWith
    (fun pid => liftWGPrefix (requireNotPending pid "wg_stop while a handshake is queued"))
    (fun pid => liftWGPrefix (purgeStagedPackets pid))
    (fun pid => liftWGPrefix (timersStop pid))
    (fun pid => liftWGPrefix (handshakeClear pid))
    (fun pid => liftWGPrefix (keypairsClear pid))
    (fun pid => liftWGPrefix (resetLastSentHandshake pid)) pid

theorem stopPeerPlain_erases (pid : PeerId) :
    ErasesStatePrefix (stopPeerPlain pid)
      (DriverTags.Control.stopPeerWith
        (fun pid => requireNotPending pid "wg_stop while a handshake is queued")
        purgeStagedPackets timersStop handshakeClear keypairsClear resetLastSentHandshake pid) :=
  DriverTags.Control.stopPeerWith_erases _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ => erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_lift _)
    (fun _ => erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_lift _)
    (fun _ => erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_lift _) pid

theorem stopPeerPlain_preserves (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    StatePrefixPreserves (fun _ w _ => Entry cs loans w) (fun _ => True)
      (stopPeerPlain pid) := by
  apply DriverTags.Control.stopPeerWith_preserves
  · intro pid
    apply native_lift
    simp only [requireNotPending]
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    cases run
    exact pre
  · exact fun pid => native_lift _ _ (purge_entry cs loans pid)
  · exact fun pid => native_lift _ _ (timers_entry cs loans pid)
  · exact fun pid => native_lift _ _ (handshake_entry cs loans pid)
  · exact fun pid => native_lift _ _ (keys_entry cs loans pid)
  · exact fun pid => native_lift _ _ (reset_entry cs loans pid)

theorem native_ambient {α : Type} (P : WGWorld → Prop) (action : AmbientM α) :
    StatePrefixPreserves (fun (_ : List Unit) w (_ : Ambient) => P w)
      (fun _ => True) (liftWGPrefix (monadLift action : WG.M α)) :=
  native_lift P _ (hoare_liftAmbient action P)

theorem stopPlain_preserves (cs : Ledger) (loans : Reservations) :
    StatePrefixPreserves (fun _ w _ => Entry cs loans w) (fun _ => True)
      (DriverTags.Control.stopWith (fun {_} a => liftWGPrefix a) stopPeerPlain) :=
  DriverTags.Control.stopWith_preserves _ _ (fun _ _ _ _ => trivial)
    stopPeerPlain (stopPeerPlain_preserves cs loans)
    (native_lift _ _ (read_entry cs loans))
    (fun b => native_ambient _ (AmbientM.branch .stopPeersIter b))
    (native_ambient _ (AmbientM.unsupported "wg_stop with handshake messages queued for the receive worker (its timing)"))
    (native_ambient _ (AmbientM.branch .stopDrainIter false))
    (native_lift _ _ (queueReset_entry cs loans))
    (native_lift _ _ (socket_entry cs loans (socketReinit_sameSocket _ _)))

theorem stop_entry (cs : Ledger) (loans : Reservations) :
    Preserves (Entry cs loans) wgStop := by
  apply native_erased (Entry cs loans)
    (DriverTags.Control.stopWith (fun {_} a => liftWGPrefix a) stopPeerPlain) wgStop
  · rw [DriverTags.Control.stop_factor]
    exact DriverTags.Control.stopWith_erases _ _ stopPeerPlain_erases
  · exact stopPlain_preserves cs loans

theorem down_entry (cs : Ledger) (loans : Reservations) :
    Preserves (Entry cs loans) wgDown := by
  rw [DriverTags.Control.down_factor]
  exact preserves_bind (running_entry cs loans false) (fun _ => stop_entry cs loans)

end Leanux.Proofs.WG.Index.LifecycleIndex
