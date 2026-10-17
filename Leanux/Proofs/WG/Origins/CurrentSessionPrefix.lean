import Leanux.Proofs.WG.Origins.CurrentSession
import Leanux.Proofs.WG.Origins.CurrentLifecycle
import Leanux.Proofs.WG.Origins.HistorySupport

/-! Current configured identity follows the existing once-only session observer
through both journal focuses and the native-to-product adapter. Incoming history
is arbitrary: these normal endpoint contracts do not certify old receipts.
The combined contract separately retains the existing reached-prefix safety. -/
namespace Leanux.Proofs.WG.CurrentSessionPrefix
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

def SessionInv (h : List (MaterialOrigin.Event SessionOrigin.Receipt))
    (w : WGWorld) : Prop :=
  ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv (h.filterMap Origins.receipt?) w

theorem observed (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => SessionInv h w) (fun _ => True)
      (SessionOrigin.observed pid) := by
  intro w ambient h hi
  obtain ⟨s,hs⟩ := Origins.sessionSource_appends pid w ambient h
  refine ⟨s,hs,True.intro,?_⟩
  cases hr : runPrefix ((SessionOrigin.observed pid).run w) ambient h with
  | mk result history =>
    cases result with
    | error e => trivial
    | ok out =>
      rcases out with ⟨⟨result,v⟩,ambient'⟩
      have native := (SessionOrigin.observed_erases pid w ambient h).symm.trans
        (congrArg Prod.fst hr)
      have view := (ProjectedAction.iff_run_ambient _ _ _).mp
        (ConfiguredMaintenance.beginSession_view pid) w ambient result v ambient' native
      constructor
      · intro cell hc
        exact hi.1 cell (view.symm.trans hc)
      · exact CurrentSession.observed_support pid w v result ambient ambient' h history
          hi.1 hi.2 hr

theorem localSession (pid : PeerId) :
    StatePrefixPreserves
      (fun h w _ => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv (Origins.sessions h) w)
      (fun _ => True) (Origins.localSession pid) := by
  have proof := StatePrefixEnsures.focus Origins.sessionEncode Origins.sessionDecode
    (by intro e; cases e <;> rfl) (observed pid)
  simpa only [SessionInv,Origins.session_filter,Origins.localSession] using proof

def StateInv (h : List RxHistory.Event) (w : World) : Prop :=
  ConfiguredIdentity.Inv w.wg ∧ CurrentIdentity.Inv (Origins.HistorySupport.sessions h) w.wg

/-- Both focuses run the original native observer once, at the history obtained
by their actual projections. The ambient endpoint is the observer's endpoint. -/
theorem session (pid : PeerId) :
    PrefixPreserves StateInv (fun _ => True) (Origins.HistoryAdapters.session pid) := by
  have proof := PrefixEnsures.focus Origins.HistoryAdapters.encode Origins.HistoryAdapters.decode
    Origins.HistoryAdapters.decode_encode (localSession pid).liftWGObserver
  simpa only [PrefixEnsures,PrefixPreserves,StateInv,Origins.HistorySupport.sessions_decoded,
    Origins.HistoryAdapters.session,Origins.HistoryAdapters.focus] using proof

/-- Existing material/history safety and stronger configured/current identity
hold for the same execution and the same output history, including safe Stop
prefixes. No endpoint is asserted after a Stop. -/
theorem session_supported (pid : PeerId) :
    PrefixPreserves
      (fun h w => Origins.HistorySupport.SupportInv h w ∧ StateInv h w)
      Origins.HistorySupport.HistorySafe (Origins.HistoryAdapters.session pid) := by
  intro w h hi
  obtain ⟨s,hs,safe,post⟩ := Origins.HistorySupport.session pid w h hi.1
  have current := (session pid w h hi.2).choose_spec.2.2
  refine ⟨s,hs,safe,?_⟩
  cases hr : (runPrefix (Origins.HistoryAdapters.session pid) w h).1 with
  | error e => trivial
  | ok out =>
    rw [hr] at post current
    exact ⟨post,current⟩

end Leanux.Proofs.WG.CurrentSessionPrefix

