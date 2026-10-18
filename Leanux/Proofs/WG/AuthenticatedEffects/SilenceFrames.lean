import Leanux.Proofs.WG.AuthenticatedEffects.InvalidMac

/-! Invalid-MAC1 receives preserve the entire WG projection except the
function-static under-load timestamp. This retains timers and all peer fields. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.WG.Cookies Leanux.Proofs.Framing Std.Do

def quietView (w : WGWorld) : WGWorld := {w with lastUnderLoad := none}

theorem loadPhase_quiet : SameView quietView loadPhase := by
  intro initial
  let P := fun w : WGWorld => quietView w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have device : Preserves P getDev := by
    unfold getDev
    apply preserves_bind read
    intro w
    cases w.dev
    · exact ambient (AmbientM.invariant "no WireGuard device in this trace's fixture")
    · exact preserves_pure _
  have expired (last : Int64) : Preserves P (birthdateTest last 1) :=
    ((birthdateTest_sameWGWorld last 1).factor quietView).wp (fun s => s = initial)
  unfold loadPhase hiddenClock64
  simp (config := { zeta := false }) only [branch, branchCmp, invariant]
  repeat' first
    | cookie_source_fact expired
    | (cookie_source_head getDev; exact device)
    | (cookie_source_head get; exact read)
    | (cookie_source_head MonadStateOf.get; exact read)
    | (cookie_source_head modify; apply hoare_modify; intro w hi; exact hi)
    | (cookie_source_lift AmbientM; exact ambient _)
    | cookie_source_step

theorem receive_bad_mac1_quiet (msg : List UInt8) (src : SkbSource)
    (w u v : WGWorld) (a b c : Ambient) (d : Device) (loaded : Bool)
    (notCookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE)
    (load : (loadPhase.run w).run (CounterWindow.record a .hsCookie false) =
      .ok ((loaded,u),b))
    (hd : u.dev = some d) (bad : mac1Computed d msg ≠ mac1Given msg)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),c)) :
    quietView v = quietView w := by
  rw [receive_bad_mac1_any msg src w u a b d loaded notCookie load hd bad] at run
  cases run
  exact (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp loadPhase_quiet
    w _ loaded u b load

end Leanux.Proofs.WG.AuthenticatedEffects
