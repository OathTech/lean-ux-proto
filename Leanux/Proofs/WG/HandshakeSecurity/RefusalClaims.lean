import Leanux.Proofs.WG.HandshakeSecurity.LookupFrames
import Leanux.Proofs.WG.HandshakeSecurity.TimestampFrames

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

private theorem skip_bind {α β : Type} (action : WG.M α) (next : α → WG.M β)
    (post : β → WGWorld → Prop)
    (tail : ∀ x, Hoare (next x) (fun _ => True) post) :
    Hoare (action >>= next) (fun _ => True) post := by
  apply hoare_bind action next (Q := fun _ _ => True) ?_ tail
  exact (hoare_iff_run_ambient _ _ _).mpr (fun _ _ _ _ _ _ _ => trivial)

private theorem out_some (peer : Option PeerId) (pid : PeerId) :
    Hoare (Queues.RxCredits.HandshakeLoans.initiationOut peer (some pid))
      (fun _ => True) (fun result _ => result = some pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b _ run
  change Except.ok ((some pid, w), CounterWindow.record a .consumeFailedPut false) =
    .ok ((result, v), b) at run
  cases run
  rfl

theorem success_returns_some (msg e ck hash t : List UInt8) (peer : Option PeerId)
    (pid : PeerId) (p : Peer) :
    Hoare (successWith (fun a => a) timestampStep msg e ck hash t peer pid p)
      (fun _ => True) (fun result _ => result = some pid) := by
  unfold successWith
  repeat' first
    | with_reducible exact out_some _ _
    | with_reducible apply skip_bind
    | (session_origin_intro_forall; try dsimp only)
    | split

private theorem native_branch (decision : Decision) (value : Bool) (w : WGWorld) (a : Ambient) :
    ((branch decision value : WG.M Bool).run w).run a =
      .ok ((value, w), CounterWindow.record a decision value) := rfl

theorem out_none_retains (peer : Option PeerId) (w v : WGWorld)
    (a b : Ambient) (result : Option PeerId)
    (run : ((Queues.RxCredits.HandshakeLoans.initiationOut peer none).run w).run a =
      .ok ((result, v), b)) : RetainsHandshake w v := by
  simp only [Queues.RxCredits.HandshakeLoans.initiationOut, Option.isNone_none,
    StateT.run_bind, native_branch, CounterWindow.except_ok_bind, ite_true] at run
  cases hr : ((peerPut peer).run w).run (CounterWindow.record a .consumeFailedPut true) with
  | error stop => simp [hr] at run
  | ok out =>
    rcases out with ⟨⟨x, state⟩, ambient⟩
    simp only [hr, CounterWindow.except_ok_bind] at run
    cases run
    exact peerPut_retains_handshake peer w _ _ _ x hr

theorem checked_none_retains (msg e ck hash t : List UInt8) (peer : Option PeerId)
    (pid : PeerId) (p : Peer) (w v : WGWorld) (a b : Ambient)
    (run : ((checkedWith (fun a => a) timestampStep msg e ck hash t peer pid p).run w).run a =
      .ok ((none, v), b)) : RetainsHandshake w v := by
  rw [checkedWith, MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨now, read, clockAmbient, clock, rest⟩ := run
  have unchanged : read = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hiddenClock64 .floodNow) (fun g : WGWorld => g = w))
    w a now read clockAmbient rfl clock
  subst read
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨rejected, tested, guardAmbient, guard, tail⟩ := rest
  have unchanged := guards_same_world (memcmp t p.latestTimestamp != .gt)
    (p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64)
    now w tested clockAmbient guardAmbient rejected guard
  subst tested
  cases rejected with
  | true =>
    simp only [ite_true] at tail
    exact out_none_retains peer w v guardAmbient b none tail
  | false =>
    simp only [Bool.false_eq_true, ite_false] at tail
    have impossible := (hoare_iff_run_ambient _ _ _).mp
      (success_returns_some msg e ck hash t peer pid p) w guardAmbient none v b trivial tail
    cases impossible

end Leanux.Proofs.WG.HandshakeSecurity
