import Leanux.Proofs.WG.Noise.SlotFrames
import Leanux.Proofs.Framing.WGTime

/-! Observation-parametric source contracts for the existing initialization
and timestamp-reset proof spines. Their original calls and failures remain. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do
theorem handshakeInit_source (pid : PeerId) (psk : Option Key) :
    handshakeInit pid psk = (do
      modifyPeer pid (fun p=>{p with handshakeEntryPeer:=some pid})
      if ←branch .handshakeInitHasPsk psk.isSome then
        modifyPeer pid (fun p=>{p with presharedKey:=psk.getD p.presharedKey})
      precomputeStaticStatic pid) := by
  have modify_eq (f : Peer → Peer) : Noise.modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  simp only [handshakeInit,IndexOwner.setPeerWord,modify_eq,bind_assoc]

theorem handshakeInit_frame_source {V : Type} (view : WGWorld → V)
    (pid : PeerId) (psk : Option Key)
    (word : SameView view (modifyPeer pid (fun p=>{p with handshakeEntryPeer:=some pid})))
    (writePsk : SameView view (modifyPeer pid (fun p=>{p with presharedKey:=psk.getD p.presharedKey})))
    (precompute : SameView view (precomputeStaticStatic pid)) :
    SameView view (handshakeInit pid psk) := by
  rw [handshakeInit_source]
  apply word.bind
  intro _
  apply (show SameView view (branch .handshakeInitHasPsk psk.isSome) from
    fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun g => view g = initial)).bind
  intro hasPsk
  cases hasPsk
  · simpa using precompute
  · exact writePsk.bind (fun _=>precompute)
theorem resetLastSentHandshake_frame_source {V : Type} (view : WGWorld → V)
    (pid : PeerId)
    (write : ∀ now,SameView view (modifyPeer pid (fun p=>{p with lastSentHandshake:=
      now-(REKEY_TIMEOUT+1:Nat).toInt64*NSEC_PER_SEC64}))) :
    SameView view (resetLastSentHandshake pid) := by
  have factor : resetLastSentHandshake pid = (do
      let now ← hiddenClock64 .resetLastSent
      modifyPeer pid (fun p => {p with
        lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64})) := by
    rfl
  rw [factor]
  exact (show SameView view (hiddenClock64 .resetLastSent : WG.M Int64) from
    fun initial => hoare_liftAmbient (AmbientM.hiddenClock64 _) (fun g => view g = initial)).bind
    write
end Leanux.Proofs.WG.Noise
