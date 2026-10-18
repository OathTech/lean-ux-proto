import Leanux.Proofs.WG.HandshakeSecurity.ResponderRemovalFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins Origins.Retaining

theorem socket_native {a : WG.M α} (frame : SameSocket a) (confirmed : List Nat) :
    Preserves (History.Native confirmed) a := by
  apply native_fields
  · apply frame.of_factor (fun s : WGOwnedView => pool {dev := s.dev})
    intro w
    funext kid
    simp only [pool, socketView, socketDevice, wgOwnedView, wgStoreView,
      Option.bind_map, Function.comp_def]
  · apply frame.of_factor (fun s : WGOwnedView => CurrentSlots.fields {dev := s.dev})
    intro w
    unfold CurrentSlots.fields RxCredits.keyWords
    cases hd : w.dev <;> simp [socketView, socketDevice, wgOwnedView, wgStoreView, hd]

theorem configuration_native {a : WG.M α} (frame : SameConfiguration a) (confirmed : List Nat) :
    Preserves (History.Native confirmed) a := by
  apply native_fields
  · apply frame.of_factor (fun s : WGOwnedView => pool {dev := s.dev})
    intro w
    funext kid
    simp only [pool, configurationView, configurationDevice, wgOwnedView, wgStoreView,
      Option.bind_map, Function.comp_def]
  · apply frame.of_factor (fun s : WGOwnedView => CurrentSlots.fields {dev := s.dev})
    intro w
    unfold CurrentSlots.fields RxCredits.keyWords
    cases hd : w.dev <;> simp [configurationView, configurationDevice, wgOwnedView, wgStoreView, hd]

theorem precompute_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (precomputeStaticStatic pid) :=
  native_fields (pool_of_material (precomputeStaticStatic_material pid))
    (CurrentSlots.precomputeStaticStatic_fields pid) confirmed

theorem resetHandshake_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (resetLastSentHandshake pid) :=
  native_fields (pool_of_material (resetLastSentHandshake_material pid))
    (CurrentSlots.resetLastSentHandshake_fields pid) confirmed

theorem initHandshake_native (pid : PeerId) (psk : Option Key) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (handshakeInit pid psk) :=
  native_fields (pool_of_material (handshakeInit_material pid psk))
    (CurrentSlots.handshakeInit_fields pid psk) confirmed

theorem peerCore_native (pid : PeerId) (key : Key) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (Peers.peerCreateCore pid key) := by
  apply native_join ?_ (CurrentSlots.peerCreateCore_preserves pid key)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  rw [Peers.peerCreateCore_run] at run
  cases run
  intro q core resident responder
  cases hd : w.dev with
  | none => simp [current, Peers.creationCoreWorld, hd] at resident
  | some d =>
    by_cases eq : pid = q
    · subst q
      simp [current, Peers.creationCoreWorld, hd, Peers.createdPeer] at resident
    · apply hi q core _ responder
      simpa [current, Peers.creationCoreWorld, hd, Std.TreeMap.getElem?_insert, eq] using resident

theorem peerCreate_native (key : Key) (psk : Option Key) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (peerCreate key psk) := by
  rw [←Peers.peerCreateFactored_eq]
  unfold Peers.peerCreateFactored
  simp (config := {zeta := false}) only [branch, branchCmp, hiddenAlloc]
  repeat' first
    | (rx_retention_head Peers.peerCreateCore; exact peerCore_native _ _ confirmed)
    | (rx_retention_head dstCacheReset
       exact sendView_native ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.dstCacheReset_view) _)
         (CurrentSlots.fields_preserves (project := id) (CurrentSlots.dstCacheReset_fields _)) confirmed)
    | (rx_retention_head handshakeInit; exact initHandshake_native _ _ confirmed)
    | (rx_retention_head resetLastSentHandshake; exact resetHandshake_native _ confirmed)
    | responder_handshake_step confirmed

theorem invalidate_native (kid : KeypairId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (do
      let key ← getKeypair kid
      setKeypair kid {key with sending := {key.sending with isValid := false}}) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨key, read, ar, getter, setter⟩ := run
  obtain ⟨same, time, d, hd, hk⟩ := KeyTimes.getKeypair_return kid w read key a ar getter
  subst read ar
  cases setter
  refine ⟨hi.1.frame ?_, CurrentSlots.fields_transport hi.2 ?_⟩
  · simpa [setKeypair, modifyDev, hd] using
      current_key_write w d kid key {key with sending := {key.sending with isValid := false}} hd hk rfl
  · unfold CurrentSlots.fields RxCredits.keyWords
    simp only [hd, Option.map_some, Option.bind_some]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext q
    by_cases eq : kid = q
    · subst q; simp [hk]
    · simp [Std.TreeMap.getElem?_insert, eq]

theorem expire_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (expireCurrentPeerKeypairs pid) := by
  let P := History.Native confirmed
  have invalid (kid : KeypairId) := invalidate_native kid confirmed
  have clear := handshakeClear_native pid confirmed
  have reset := resetHandshake_native pid confirmed
  have read := readPeer_native pid confirmed
  have effect {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  change Preserves P _
  routing_tx_source [expireCurrentPeerKeypairs, requireNotPending, branch, invariant]
    using [invalid, clear, reset, read, effect]

end Leanux.Proofs.WG.HandshakeSecurity.Responder
