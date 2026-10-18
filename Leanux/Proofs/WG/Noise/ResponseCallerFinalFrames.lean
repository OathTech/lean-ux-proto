import Leanux.Proofs.WG.Noise.ResponseSuffixTagFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ResponseCaller
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Origins
open ResponseSuffix

/-- Current tags agree with the most recently completed actual receipt. -/
def NativeLastTags (history : List Event) (current : WGWorld) : Prop :=
  ∀ event, history.getLast? = some event →
    tags current = event.receipt.after.tagAt

private theorem lift_lastTags {α : Type} (action : WG.M α)
    (frame : ∀ g ambient result final after,
      ((action.run g).run ambient) = .ok ((result, final), after) →
        tags final = tags g) :
    StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
      (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift
  · intro h g ambient pre; trivial
  · intro h g ambient result final after pre run event last
    exact (frame g ambient result final after run).trans (pre event last)

private theorem receipt_lastTags {α : Type} (action : WG.M α)
    (event : WGRunWitness α → Event)
    (projection : ∀ r, (event r).receipt.after.tagAt = tags r.after) :
    StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
      (receiptWGObserved (liftWGPrefix action) event) := by
  unfold receiptWGObserved
  have captured : StatePrefixEnsures (fun h g _ => NativeLastTags h g)
      (fun _ => True) (captureWGRun action)
      (fun r _ g _ => tags g = (event r).receipt.after.tagAt) := by
    apply StatePrefixEnsures.captureWGRun action
    · intro h g ambient prior; trivial
    · intro h g ambient result final after prior run
      exact (projection ⟨result, g, final, ambient, after⟩).symm
  apply StatePrefixEnsures.bind captured
  intro r
  apply StatePrefixEnsures.bind
    (Q := fun _ h g _ => NativeLastTags h g)
  · apply StatePrefixEnsures.emit (event r)
    · intro h g ambient prior; trivial
    · intro h g ambient prior lastEvent last
      have same : event r = lastEvent := by simpa using last
      subst lastEvent
      exact prior
  · intro _
    exact StatePrefixEnsures.pure r.value (fun _ _ _ _ => True.intro)
      (fun _ _ _ prior => prior)

/-- Every non-receipt helper of the original response caller has a concrete
tag frame. The creator and session receipts reset the invariant to their
actual resulting tags. Stops retain their original outcome. -/
theorem observe_lastTags (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
      (observe pid) := by
  have pureLast {α : Type} (value : α) :
      StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
        (pure value : Obs α) :=
    StatePrefixEnsures.pure value (fun _ _ _ _ => True.intro)
      (fun _ _ _ prior => prior)
  have created := receipt_lastTags (createResponse pid) (.created pid) (fun _ => rfl)
  have session := receipt_lastTags (beginSession pid) (.session pid) (fun _ => rfl)
  have ambientLast {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
        (liftWGPrefix (StateT.lift a : WG.M α)) := by
    apply lift_lastTags
    intro g ambient result final after run
    exact (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant a (fun current => tags current = tags g))
      g ambient result final after rfl run
  have clock (site : HiddenSite) :
      StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
        (liftWGPrefix (hiddenClock64 site : WG.M Int64)) :=
    lift_lastTags _ (clock_tag_frame site)
  have stamp (now : Int64) :
      StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
        (liftWGPrefix (do let p ← getPeer pid; setPeer pid {p with lastSentHandshake := now})) :=
    lift_lastTags _ (lastSent_tag_frame pid now)
  have mac (msg : List UInt8) :
      StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
        (liftWGPrefix (addMacToPacket pid msg)) := by
    apply lift_lastTags
    intro g ambient result final after run
    exact addMacToPacket_spec_tagMap_variant pid msg g.dev g ambient result final after rfl run
  have derived :
      StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
        (liftWGPrefix (timersSessionDerived pid)) := by
    apply lift_lastTags
    intro g ambient result final after run
    exact derived_tag_frame pid g.dev g ambient result final after rfl run
  have traversal :
      StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
        (liftWGPrefix (timersTraversal pid)) := by
    apply lift_lastTags
    intro g ambient result final after run
    exact traversal_tag_frame pid g.dev g ambient result final after rfl run
  have sent :
      StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
        (liftWGPrefix (timersAnyAuthenticatedPacketSent pid)) := by
    apply lift_lastTags
    intro g ambient result final after run
    exact delTimer_tag_frame pid .sendKeepalive g.dev g ambient result final after rfl run
  have send (msg : List UInt8) :
      StatePrefixPreserves (fun h g _ => NativeLastTags h g) (fun _ => True)
        (liftWGPrefix (sendBufferToPeer pid msg)) := by
    apply lift_lastTags
    intro g ambient result final after run
    exact sendBufferToPeer_spec_tagMap_variant pid msg g.dev g ambient result final after rfl run
  unfold observe HandshakeSources.responseWith
  simp only [ops]
  change StatePrefixEnsures (fun h g _ => NativeLastTags h g) (fun _ => True) _
    (fun _ h g _ => NativeLastTags h g)
  repeat' first
    | (maintenance_head receiptWGObserved; first | exact created | exact session)
    | (maintenance_lift_action_head hiddenClock64; exact clock _)
    | (maintenance_lift_action_head Bind.bind; exact stamp _)
    | (maintenance_lift_action_head addMacToPacket; exact mac _)
    | (maintenance_lift_action_head timersSessionDerived; exact derived)
    | (maintenance_lift_action_head timersTraversal; exact traversal)
    | (maintenance_lift_action_head timersAnyAuthenticatedPacketSent; exact sent)
    | (maintenance_lift_action_head sendBufferToPeer; exact send _)
    | (maintenance_lift_action_head branch; exact ambientLast (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambientLast (AmbientM.invariant _))
    | (maintenance_head Pure.pure; exact pureLast _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h g _ => NativeLastTags h g))
    | maintenance_intro
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction

theorem observe_normal_lastTags (pid : PeerId) (g final : WGWorld)
    (ambient after : Ambient) (history : List Event)
    (run : runWGPrefix (observe pid) g ambient [] =
      (.ok (((), final), after), history)) : NativeLastTags history final := by
  have framed := observe_lastTags pid g ambient []
    (by intro event last; cases last)
  obtain ⟨suffix, appended, safe, normal⟩ := framed
  have raw := run
  simp only [runWGPrefix, runStatePrefix] at raw
  simpa only [raw] using normal

theorem observeNative_lastTags (pid : PeerId) :
    Campaign2.Ensures (observeNative pid) (fun _ => True)
      (fun history final => ∀ event, history.getLast? = some event →
        final.tagAt = event.receipt.after.tagAt) := by
  intro g ambient history final after pre run
  cases observed : runWGPrefix (observe pid) g ambient [] with
  | mk result events =>
    cases result with
    | error stop =>
      simp only [StateT.run, observeNative, observed, Except.map] at run
      cases run
    | ok result =>
      obtain ⟨⟨u, current⟩, inputs⟩ := result
      cases u
      simp only [StateT.run, observeNative, observed, Except.map, Except.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
      exact observe_normal_lastTags pid g current ambient inputs events observed

end Leanux.Proofs.WG.Noise.ResponseCaller
