import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointCoverage

/-! Structural refinement of the seven receive helper families. Staging, queued
work and peer release retain their distinct caller contracts. The sole new
interior boundary is the actual observed timer arm, not any enclosing helper. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

def consumePoints (inside : ChildPoints) (other : Points.ChildPoints) : Points.ChildPoints :=
  fun token w h u middle => match token with
    | .endpoint pid ep => ∃ site, Point inside (endpointShape pid ep) w h site u middle
    | .keyRelease kid => ∃ site, Point inside (keyReleaseShape kid true) w h site u middle
    | .handshakeTimer pid => ∃ site, Point inside (handshakeTimerShape pid) w h site u middle
    | .authenticated pid => ∃ site, Point inside (authenticatedShape pid) w h site u middle
    | .lookup protocol bytes => ∃ site, Point inside (lookupShape protocol bytes) w h site u middle
    | .traversal pid => ∃ site, Point inside (traversalShape pid) w h site u middle
    | .received pid => ∃ site, Point inside (receivedShape pid) w h site u middle
    | token => other token w h u middle

variable {native inside : ChildPoints} {nativeOther insideOther : Points.ChildPoints}
variable {Good : History → World → Prop}

noncomputable def helper_contract (token : Points.Child) (shape : Shape token.action)
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (nativeCases : ∀ w h u middle, consumePoints native nativeOther token w h u middle ↔
      ∃ site, Point native shape w h site u middle)
    (insideCases : ∀ w h u middle, consumePoints inside insideOther token w h u middle ↔
      ∃ site, Point inside shape w h site u middle) :
    Points.ChildSourceContract (consumePoints native nativeOther) (consumePoints inside insideOther) Good token where
  remainder := fun w h u middle point =>
    Classical.choose ((Classical.choose_spec ((nativeCases w h u middle).mp point)).residual children)
  continuation := by
    intro w h u middle point
    exact (Classical.choose_spec ((Classical.choose_spec ((nativeCases w h u middle).mp point)).residual children)).run
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := (nativeCases w h u middle).mp point
    exact (insideCases w h u middle).mpr ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := (insideCases w h u middle).mp point
    exact point.safe carrierGood children before

noncomputable def consume_children
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (queued : ∀ pid, Points.ChildSourceContract (consumePoints native nativeOther)
      (consumePoints inside insideOther) Good (.queued pid))
    (staging : ∀ pid, Points.ChildSourceContract (consumePoints native nativeOther)
      (consumePoints inside insideOther) Good (.staging pid))
    (release : ∀ peer, Points.ChildSourceContract (consumePoints native nativeOther)
      (consumePoints inside insideOther) Good (.release peer)) :
    Points.ChildContracts (consumePoints native nativeOther) (consumePoints inside insideOther) Good where
  contract := by
    intro token
    cases token with
    | endpoint pid ep =>
      exact helper_contract (.endpoint pid ep) (endpointShape pid ep) carrierGood children
        (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    | keyRelease kid =>
      exact helper_contract (.keyRelease kid) (keyReleaseShape kid true) carrierGood children
        (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    | handshakeTimer pid =>
      exact helper_contract (.handshakeTimer pid) (handshakeTimerShape pid) carrierGood children
        (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    | authenticated pid =>
      exact helper_contract (.authenticated pid) (authenticatedShape pid) carrierGood children
        (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    | lookup protocol bytes =>
      exact helper_contract (.lookup protocol bytes) (lookupShape protocol bytes) carrierGood children
        (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    | traversal pid =>
      exact helper_contract (.traversal pid) (traversalShape pid) carrierGood children
        (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    | received pid =>
      exact helper_contract (.received pid) (receivedShape pid) carrierGood children
        (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    | queued pid => exact queued pid
    | staging pid => exact staging pid
    | release peer => exact release peer

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
