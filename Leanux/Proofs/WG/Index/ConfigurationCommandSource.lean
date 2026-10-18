import Leanux.Proofs.WG.Index.ConfigurationCreationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

theorem noneOut_entry (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs) (ret : Int) :
    Preserves (Entry cs loans) (do
      peerPut none
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  change Except.ok ((ret,w),CounterWindow.record (CounterWindow.record a .peerPutNull true)
    .peerZeroPsk attrs.presharedKey.isSome)=.ok ((result,v),b) at run
  cases run
  exact pre

theorem update_acquired_entry (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Hoare (peerConfigUpdateSource attrs (some pid) flags psk pid)
      (Acquired cs loans (some pid)) (fun _=>Entry cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  obtain ⟨paid,slot,entry,member⟩ := pre
  subst pid
  exact update_entry cs loans attrs paid flags psk w a result v b ⟨entry,member⟩ run

theorem create_update_entry (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (psk : Option Key) (flags : UInt32) :
    Preserves (Entry cs loans) (do
      match ← peerCreate key psk with
      | .error code =>
        _ ← branch .peerCreateErr true
        peerPut none
        _ ← branch .peerZeroPsk attrs.presharedKey.isSome
        pure code
      | .ok pid =>
        _ ← branch .peerCreateErr false
        peerGet pid
        peerConfigUpdateSource attrs (some pid) flags psk pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨created,u,c,creation,tail⟩ := run
  cases created with
  | error code =>
    have current := (hoare_iff_run_ambient _ _ _).mp
      (creation_entry cs loans key psk) w a (.error code) u c pre creation
    change ((do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure code : WG.M Int).run u).run
      (CounterWindow.record c .peerCreateErr true)=.ok ((result,v),b) at tail
    exact (hoare_iff_run_ambient _ _ _).mp (noneOut_entry cs loans attrs code)
      u _ result v b current tail
  | ok pid =>
    change ((peerGet pid >>= fun _=>peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run
      (CounterWindow.record c .peerCreateErr false)=.ok ((result,v),b) at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,z,d,acquire,finish⟩ := tail
    cases ignored
    exact (hoare_iff_run_ambient _ _ _).mp
      (update_acquired_entry cs loans attrs flags psk pid) z d result v b
      (creation_acquire_entry cs loans key psk w u z a c d pid pre creation acquire) finish

theorem acquired_entry (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    Hoare (peerCommandAcquiredWith (fun {_} action=>action) peerCreate peerGet
      (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (peerConfigUpdateSource attrs) key psk flags peer)
      (Acquired cs loans peer) (fun _=>Entry cs loans) := by
  cases peer with
  | some pid =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    change ((peerConfigUpdateSource attrs (some pid) flags psk pid).run w).run
      (CounterWindow.record a .peerNotFound false)=.ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp
      (update_acquired_entry cs loans attrs flags psk pid) w _ result v b pre run
  | none =>
    change Preserves (Entry cs loans) _
    unfold peerCommandAcquiredWith
    unfold WG.andM
    simp (config:={zeta:=false}) only [branch,invariant]
    repeat' first
      | contradiction
      | (env_bind_head peerCreate; exact create_update_entry cs loans attrs key psk _)
      | (rx_retention_head getDev; exact read_entry cs loans)
      | (env_bind_head peerPut; exact noneOut_entry cs loans attrs _)
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step

end Leanux.Proofs.WG.Index.ConfigurationIndex
