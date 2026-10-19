import Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutsideInitiation
import Leanux.Proofs.WG.AuthenticatedEffects.MacRefusal
import Leanux.Proofs.WG.AuthenticatedEffects.SilenceFrames

/-! Full native MAC-refusal projection. Only the function-static load timestamp,
cookie secret/birthdate and the two rate-limit tables are excluded. All peer,
keypair, timer, index, queue and other WG fields remain visible. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.MacWorld
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Cookies
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def view (w : WGWorld) : WGWorld :=
  { w with
    dev := w.dev.map cookieDevice
    lastUnderLoad := none
    ratelimiter := {w.ratelimiter with table := [],table6 := []} }

private theorem read (P : WGWorld → Prop) : Preserves P (get : WG.M WGWorld) :=
  hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
private theorem get_device (P : WGWorld → Prop) : Preserves P getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a d v b hi run
  exact (Queues.RxCredits.DecryptCarrier.getDev_current a b run).1 ▸ hi

private theorem edit (initial : WGWorld) (f : Device → Device)
    (same : ∀ d, cookieDevice (f d) = cookieDevice d) :
    Preserves (fun w => view w = initial) (modifyDev f) := by
  apply hoare_modify
  intro w hi
  simpa only [view,modifyDev,Option.map_map,Function.comp_def,same] using hi

theorem make_cookie (src : SkbSource) : SameView view (makeCookie src) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold makeCookie hiddenClock64 hidden
  simp only [branch]
  repeat' first
    | (cookie_source_head getDev; exact get_device _)
    | (cookie_source_head modifyDev; exact edit initial _ (fun _ => rfl))
    | (cookie_source_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => view w = initial))
    | (cookie_source_lift AmbientM; exact hoare_liftAmbient _ _)
    | cookie_source_step

theorem ratelimiter (src : SkbSource) : SameView view (ratelimiterAllow src) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold ratelimiterAllow hiddenClock hiddenAlloc
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' first
    | (cookie_source_head get; exact read _)
    | (cookie_source_head MonadStateOf.get; exact read _)
    | (cookie_source_head modify; apply hoare_modify; intro w hi; dsimp only; split <;> exact hi)
    | (cookie_source_lift AmbientM; exact hoare_liftAmbient _ _)
    | cookie_source_step

theorem validate (msg : Key) (src : SkbSource) (loaded : Bool) :
    SameView view (cookieValidatePacket msg src loaded) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold cookieValidatePacket
  simp only [branch]
  repeat' first
    | (cookie_source_head getDev; exact get_device _)
    | (cookie_source_head makeCookie; exact (make_cookie _).wp (fun v => v = initial))
    | (cookie_source_head ratelimiterAllow; exact (ratelimiter _).wp (fun v => v = initial))
    | (cookie_source_lift AmbientM; exact hoare_liftAmbient _ _)
    | cookie_source_step

theorem load : SameView view loadPhase :=
  loadPhase_quiet.of_factor view view (fun _ => rfl)

theorem refused (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState)
    (w u v : WGWorld) (a b c : Ambient)
    (notCookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE)
    (loadRun : (loadPhase.run w).run (record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b = .ok ((state,v),c))
    (rejected : state = .invalid ∨ state = .ratelimited) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),invalidDropEntry loaded c) ∧ view v = view w := by
  refine ⟨(receive_mac_refused msg src loaded state w u v a b c notCookie loadRun mac rejected).1,?_⟩
  exact ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp (validate msg src loaded) u b state v c mac).trans
    ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp load w _ loaded u b loadRun)

end Leanux.Proofs.WG.AuthenticatedEffects.MacWorld
