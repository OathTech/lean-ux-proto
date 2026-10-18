import Leanux.Proofs.WG.HandshakeSecurity.ResponderHandshakeControl

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits

theorem source_peer_authorized (entry : Authorized confirmed w) (device : w.dev = some d)
    (resident : d.peers[pid]? = some p) (f : Peer → Peer)
    (same : ∀ p, (f p).keypairCurrent = p.keypairCurrent) (a b : Ambient)
    (run : ((setPeer pid (f p)).run w).run a = .ok ((result, v), b)) : Authorized confirmed v := by
  have written : v = {w with dev := some {d with peers := d.peers.insert pid (f p)}} := by
    simpa [setPeer, modifyDev, device, Except.map] using (congrArg (fun out => out.map (fun x => x.1.2)) run).symm
  rw [written]
  exact entry.frame (current_peer_write w d pid p (f p) device resident (same p))

theorem keepalive_authorized (pid : PeerId) (confirmed : List Nat) :
    Preserves (Authorized confirmed) (sendKeepalive pid) := by
  have ambient_state {α : Type} (action : AmbientM α) (a b : Ambient)
      {w v : WGWorld} {result : α}
      (run : (((monadLift action : WG.M α)).run w).run a = .ok ((result, v), b)) : v = w :=
    (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient action (· = w)) w a result v b rfl run
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  unfold sendKeepalive at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p, read, ar, getter, run⟩ := run
  obtain ⟨same, time, d, device, resident⟩ := getPeer_normal pid w read p a ar getter
  subst read ar
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨empty, guarded, ag, guard, run⟩ := run
  have same := ambient_state (AmbientM.branch .keepaliveStagedEmpty p.staged.isEmpty) a ag guard
  subst guarded
  cases empty with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at run
    exact (hoare_iff_run_ambient _ _ _).mp (sendStagedPackets_authorized pid confirmed) w ag result v b entry run
  | true =>
    simp only [ite_true, MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨allocated, read, aa, alloc, failed, guarded, af, guard, run⟩ := run
    have same := ambient_state (AmbientM.hiddenAlloc .keepaliveSkb) ag aa alloc
    subst read
    have same := ambient_state (AmbientM.branch .keepaliveNoMem (!allocated)) aa af guard
    subst guarded
    cases failed with
    | true =>
      simp only [ite_true] at run
      cases run
      exact entry
    | false =>
      simp only [Bool.false_eq_true, ite_false, MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨dev, read, ad, getter, ignored, staged, stagedAmbient, write, run⟩ := run
      obtain ⟨same, time, _⟩ := DecryptCarrier.getDev_current af ad getter
      subst read ad
      have kept := source_peer_authorized entry device resident
        (fun p => {p with staged := p.staged ++ [{mtu := dev.mtu}]}) (fun _ => rfl) af stagedAmbient write
      exact (hoare_iff_run_ambient _ _ _).mp (sendStagedPackets_authorized pid confirmed)
        staged stagedAmbient result v b kept run

theorem reply_authorized (src : SkbSource) (bytes : List UInt8) (confirmed : List Nat) :
    Preserves (Authorized confirmed) (sendBufferAsReplyToSkb src bytes) := by
  unfold sendBufferAsReplyToSkb
  simp (config := {zeta := false}) only [branch, invariant, hiddenAlloc]
  repeat' first
    | (rx_retention_head endpointFromSkb
       exact (endpointFromSkb_sameWGStore _).wp (fun s => Authorized confirmed {dev := s.dev}))
    | (rx_retention_head send4
       exact sendView_authorized ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.send4_view) _ _ _ _ _) confirmed)
    | (rx_retention_head send6
       exact sendView_authorized ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.send6_view) _ _ _ _ _) confirmed)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Authorized confirmed))
    | rx_retention_step

namespace HandshakeControl

theorem keepalive (pid : PeerId) : Preserves (Inv confirmed) (sendKeepalive pid) :=
  authorized ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive) pid)
    (keepalive_authorized pid confirmed)

theorem sendCookie (msg : List UInt8) (src : SkbSource) : Preserves (Inv confirmed) (sendHandshakeCookie msg src) := by
  apply authorized ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.sendCookie) msg src)
  unfold sendHandshakeCookie
  apply preserves_bind
  · exact cookie_authorized (cookieMessageCreate_sameCookie _ _ _) confirmed
  · intro bytes; exact reply_authorized src bytes confirmed

end HandshakeControl
end Leanux.Proofs.WG.HandshakeSecurity.Responder
