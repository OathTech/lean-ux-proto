import Leanux.Proofs.WG.Noise.DriverTagFrames
import Leanux.Proofs.WG.Noise.ReceptionCallerSource
import Leanux.Proofs.WG.Noise.PeerCreationClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Lifetimes

/-! Source validity and concrete capture. These declarations use native source
executions; the pure model above never equates an invented zero with a birth. -/
namespace DriverTags
open Leanux.Proofs.Logged Leanux.Proofs.Framing

def PeerCreateValid (r : PeerCreateReceipt) : Prop :=
  ∃ g ambient final after,
    r.before = Campaign2.snapshot g ambient ∧
    r.after = Campaign2.snapshot final after ∧
    ((peerCreate r.publicKey r.presharedKey).run g).run ambient =
      .ok ((r.result,final),after)

def EventValid : DriverTagEvent → Prop
  | .helper r => ReceptionCaller.ReceiptValid r
  | .peerCreate r => PeerCreateValid r

def ValidHistory (events : List DriverTagEvent) : Prop :=
  ∀ event ∈ events, EventValid event

def NativeCoverage (entry : TagMap) (events : List DriverTagEvent) (g : WGWorld) : Prop :=
  DriverTagMapCoverage entry events (responseTagMap g.dev)

theorem PeerCreateValid.effect {r : PeerCreateReceipt} (valid : PeerCreateValid r) :
    PeerCreateEffect r := by
  obtain ⟨g,ambient,final,after,beforeEq,afterEq,run⟩ := valid
  constructor
  · rw [afterEq, beforeEq, peerStampStore_snapshot, peerStampStore_snapshot]
    cases result : r.result with
    | error code =>
      exact Peers.peerCreate_exact r.publicKey r.presharedKey g final (.error code) ambient after
        (by simpa only [result] using run)
    | ok pid =>
      exact Peers.peerCreate_exact r.publicKey r.presharedKey g final (.ok pid) ambient after
        (by simpa only [result] using run)
  · have effect := peerCreate_tag_map r.publicKey r.presharedKey r.before
      g ambient r.result final after (by rw [beforeEq]) run
    intro target
    cases result : r.result <;> simpa only [result, ← afterEq] using effect target

theorem event_effect {event : DriverTagEvent} (valid : EventValid event) : event.Effect := by
  cases event with
  | helper r => exact valid.effect
  | peerCreate r => exact valid.effect

def helperReceipt {α : Type} (operation : TagOperation) (wrap : α → TagReturn)
    (r : WGRunWitness α) : DriverTagEvent :=
  .helper (ReceptionCaller.receipt operation wrap r)

def birthReceipt (key : Key) (psk : Option Key)
    (r : WGRunWitness (Except Int PeerId)) : DriverTagEvent :=
  .peerCreate ⟨key,psk,Campaign2.snapshot r.before r.ambientBefore,r.value,
    Campaign2.snapshot r.after r.ambientAfter⟩

abbrev Obs := WGPrefix DriverTagEvent

def recordHelper {α : Type} (operation : TagOperation) (wrap : α → TagReturn)
    (action : WG.M α) : Obs α :=
  receiptWGObserved (liftWGPrefix action) (helperReceipt operation wrap)

def peerCreateObserved (key : Key) (psk : Option Key) : Obs (Except Int PeerId) :=
  receiptWGObserved (liftWGPrefix (peerCreate key psk)) (birthReceipt key psk)

theorem helperReceipt_valid {α : Type} (operation : TagOperation) (wrap : α → TagReturn)
    (action : WG.M α)
    (mapped : (do let x ← action; pure (wrap x)) = runTagOperation operation)
    (r : WGRunWitness α) (run : r.Valid action) :
    EventValid (helperReceipt operation wrap r) := by
  refine ⟨r.before,r.ambientBefore,r.after,r.ambientAfter,rfl,rfl,?_⟩
  change ((runTagOperation operation).run r.before).run r.ambientBefore =
    .ok ((wrap r.value,r.after),r.ambientAfter)
  rw [← mapped]
  change ((action.run r.before).run r.ambientBefore >>= fun ((x,g),ambient) =>
    Except.ok ((wrap x,g),ambient)) = _
  rw [run]
  rfl

theorem birthReceipt_valid (key : Key) (psk : Option Key)
    (r : WGRunWitness (Except Int PeerId)) (run : r.Valid (peerCreate key psk)) :
    EventValid (birthReceipt key psk r) :=
  ⟨r.before,r.ambientBefore,r.after,r.ambientAfter,rfl,rfl,run⟩

theorem recordHelper_erases {α : Type} (operation : TagOperation) (wrap : α → TagReturn)
    (action : WG.M α) : ErasesStatePrefix (recordHelper operation wrap action) action :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem peerCreateObserved_erases (key : Key) (psk : Option Key) :
    ErasesStatePrefix (peerCreateObserved key psk) (peerCreate key psk) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem ValidHistory.snoc {events : List DriverTagEvent} {event : DriverTagEvent}
    (prior : ValidHistory events) (valid : EventValid event) :
    ValidHistory (events ++ [event]) := by
  intro e member
  rcases List.mem_append.mp member with member | member
  · exact prior e member
  · have same : e = event := by simpa using member
    subst e
    exact valid

theorem receipt_valid {α : Type} (action : WG.M α) (event : WGRunWitness α → DriverTagEvent)
    (valid : ∀ r, r.Valid action → EventValid (event r)) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory
      (receiptWGObserved (liftWGPrefix action) event) := by
  unfold receiptWGObserved
  have captured : StatePrefixEnsures (fun h _ _ => ValidHistory h) ValidHistory
      (captureWGRun action) (fun r h _ _ => ValidHistory h ∧ EventValid (event r)) := by
    apply StatePrefixEnsures.captureWGRun action
    · intro h g ambient prior; exact prior
    · intro h g ambient value final after prior run
      exact ⟨prior,valid _ run⟩
  apply StatePrefixEnsures.bind captured
  intro r
  apply StatePrefixEnsures.bind (Q := fun _ h _ _ => ValidHistory h)
  · apply StatePrefixEnsures.emit (event r)
    · intro h g ambient prior; exact prior.1.snoc prior.2
    · intro h g ambient prior; exact prior.1.snoc prior.2
  · intro _
    exact StatePrefixEnsures.pure r.value (fun _ _ _ prior => prior) (fun _ _ _ prior => prior)

theorem receipt_coverage {α : Type} (entry : TagMap) (action : WG.M α)
    (event : WGRunWitness α → DriverTagEvent)
    (before : ∀ r, (event r).before = Campaign2.snapshot r.before r.ambientBefore)
    (after : ∀ r, (event r).after = Campaign2.snapshot r.after r.ambientAfter)
    (valid : ∀ r, r.Valid action → EventValid (event r)) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (receiptWGObserved (liftWGPrefix action) event) := by
  unfold receiptWGObserved
  have captured : StatePrefixEnsures (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (captureWGRun action) (fun r h g _ =>
        DriverTagMapCoverage entry h (event r).before.tagAt ∧
        (event r).Effect ∧ (event r).after.tagAt = responseTagMap g.dev) := by
    apply StatePrefixEnsures.captureWGRun action
    · intro h g ambient prior; trivial
    · intro h g ambient value final inputs prior run
      refine ⟨?_,event_effect (valid _ run),?_⟩
      · rw [before]; exact prior
      · rw [after]; rfl
  apply StatePrefixEnsures.bind captured
  intro r
  apply StatePrefixEnsures.bind (Q := fun _ h g _ => NativeCoverage entry h g)
  · apply StatePrefixEnsures.emit (event r)
    · intro h g ambient prior; trivial
    · intro h g ambient prior
      change DriverTagMapCoverage entry (h ++ [event r]) (responseTagMap g.dev)
      rw [← prior.2.2]
      exact prior.1.receipt _ prior.2.1
  · intro _
    exact StatePrefixEnsures.pure r.value (fun _ _ _ _ => True.intro) (fun _ _ _ prior => prior)

theorem recordHelper_valid {α : Type} (operation : TagOperation) (wrap : α → TagReturn)
    (action : WG.M α)
    (mapped : (do let x ← action; pure (wrap x)) = runTagOperation operation) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory
      (recordHelper operation wrap action) :=
  receipt_valid action _ (helperReceipt_valid operation wrap action mapped)

theorem recordHelper_coverage {α : Type} (entry : TagMap) (operation : TagOperation)
    (wrap : α → TagReturn) (action : WG.M α)
    (mapped : (do let x ← action; pure (wrap x)) = runTagOperation operation) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (recordHelper operation wrap action) :=
  receipt_coverage entry action _ (fun _ => rfl) (fun _ => rfl)
    (helperReceipt_valid operation wrap action mapped)

theorem peerCreateObserved_valid (key : Key) (psk : Option Key) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory
      (peerCreateObserved key psk) :=
  receipt_valid _ _ (birthReceipt_valid key psk)

theorem peerCreateObserved_coverage (entry : TagMap) (key : Key) (psk : Option Key) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (peerCreateObserved key psk) :=
  receipt_coverage entry _ _ (fun _ => rfl) (fun _ => rfl) (birthReceipt_valid key psk)

/-- The current normal-state coverage and all-outcome validity are distinct.
A failed primitive has no asserted final state or fabricated receipt. -/
def NativeInv (entry : TagMap) (events : List DriverTagEvent) (g : WGWorld) : Prop :=
  NativeCoverage entry events g ∧ ValidHistory events

theorem combine {α : Type} (entry : TagMap) (action : Obs α)
    (coverage : StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True) action)
    (valid : StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory action) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory action := by
  intro g ambient h prior
  obtain ⟨suffix,appends,_,normal⟩ := coverage g ambient h prior.1
  obtain ⟨_,_,safe,_⟩ := valid g ambient h prior.2
  refine ⟨suffix,appends,safe,?_⟩
  cases result : (runPrefix (action.run g) ambient h).1 with
  | error stop => trivial
  | ok out =>
    have kept : NativeCoverage entry (runPrefix (action.run g) ambient h).2 out.1.2 := by
      simpa only [result] using normal
    exact ⟨kept,safe⟩

theorem lift_retained {α : Type} (entry : TagMap) (action : WG.M α)
    (frame : ∀ g ambient result final after,
      (action.run g).run ambient = .ok ((result,final),after) →
      TagsRetained (responseTagMap g.dev) (responseTagMap final.dev)) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift
  · intro h g ambient prior; exact prior.2
  · intro h g ambient result final after prior run
    exact ⟨prior.1.final_retained (frame g ambient result final after run),prior.2⟩

theorem lift_exact {α : Type} (entry : TagMap) (action : WG.M α)
    (frame : ∀ g ambient result final after,
      (action.run g).run ambient = .ok ((result,final),after) →
      responseTagMap final.dev = responseTagMap g.dev) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix action) := by
  apply lift_retained entry action
  intro g ambient result final after run
  rw [frame g ambient result final after run]
  exact TagsRetained.refl _

theorem pure_preserves {α : Type} (entry : TagMap) (value : α) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (pure value : Obs α) :=
  StatePrefixEnsures.pure value (fun _ _ _ prior => prior.2) (fun _ _ _ prior => prior)

theorem recordHelper_preserves {α : Type} (entry : TagMap) (operation : TagOperation)
    (wrap : α → TagReturn) (action : WG.M α)
    (mapped : (do let x ← action; pure (wrap x)) = runTagOperation operation) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (recordHelper operation wrap action) :=
  combine entry _ (recordHelper_coverage entry operation wrap action mapped)
    (recordHelper_valid operation wrap action mapped)

theorem peerCreateObserved_preserves (entry : TagMap) (key : Key) (psk : Option Key) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (peerCreateObserved key psk) :=
  combine entry _ (peerCreateObserved_coverage entry key psk) (peerCreateObserved_valid key psk)

end DriverTags
end Leanux.Proofs.WG.Noise
