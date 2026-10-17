import Leanux.Proofs.WG.Noise.Slots
import Leanux.WG.Timers

/-! Current timer effects include their wheel updates. These contracts are
separate from the legacy exact-peer statements retained in ArmingSource. -/

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem delTimer_wheel_exact (pid : PeerId) (timer : PeerTimer) (p : Peer) :
    Ensures (delTimer pid timer) (fun g => peerAt g pid = some p)
      (fun _ g => peerAt g pid = some ((p.setTimer timer none).setWheel timer none)) := by
  exact (ensures_iff _ _ _).mpr
    (modifyPeer_exact_spec pid (fun p => (p.setTimer timer none).setWheel timer none) p)

theorem timersHandshakeComplete_wheel_effect (pid : PeerId) (site : HiddenSite) (p : Peer) :
    Ensures (timersHandshakeComplete pid site) (fun g => peerAt g pid = some p)
      (fun _ g => ∃ now, peerAt g pid = some
        { ((p.setTimer .retransmitHandshake none).setWheel .retransmitHandshake none) with
          timerHandshakeAttempts := 0, sentLastminuteHandshake := false,
          walltimeLastHandshake := now }) := by
  let finish : WG.M Unit := do
    modifyPeer pid (fun p => (p.setTimer .retransmitHandshake none).setWheel .retransmitHandshake none)
    modifyPeer pid (fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false})
    let now ← hidden site
    modifyPeer pid (fun p => {p with walltimeLastHandshake := now})
  have modify_eq (f : Peer → Peer) : modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have factor : timersHandshakeComplete pid site = finish := by
    simp only [timersHandshakeComplete, finish, delTimer, modify_eq, bind_assoc]
  rw [factor]
  let p1 := (p.setTimer .retransmitHandshake none).setWheel .retransmitHandshake none
  let p2 := {p1 with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}
  change Ensures (modifyPeer pid _ >>= fun _ => modifyPeer pid _ >>= fun _ =>
    (hidden site : WG.M (List UInt8)) >>= fun now => modifyPeer pid _) _ _
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (modifyPeer_exact_spec pid _ p)) ?_
  intro _
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (modifyPeer_exact_spec pid _ p1)) ?_
  intro _
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.hidden site) (fun g => peerAt g pid = some p2))) ?_
  intro now g ambient x g' ambient' hp hr
  exact ⟨now, (ensures_iff _ _ _).mpr
    (modifyPeer_exact_spec pid (fun p => {p with walltimeLastHandshake := now}) p2)
      g ambient x g' ambient' hp hr⟩

end Leanux.Proofs.WG.TimerDiscipline
