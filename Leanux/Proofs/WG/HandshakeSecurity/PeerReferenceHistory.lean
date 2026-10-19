import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceSocketFrames
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceEntrySource

/-! Positive-reference entry certificates on the existing exchange journal.
The observer is unchanged: a completed native receipt retains its real entry
world, and an inner Stop retains every previously certified receipt. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def Safe (history : List E) : Prop :=
  ∀ event ∈ history, Inv (EntryFormat.before event) ∧ EntryFormat.valid event

def StateInv (history : List E) (w : WGWorld) : Prop := (Safe (E := E)) history ∧ Inv w

abbrev Observed (action : WGPrefix E α) :=
  StatePrefixPreserves (fun h w _ => StateInv (E := E) h w) (Safe (E := E)) action

theorem safe_nil : (Safe (E := E)) [] := by simp [Safe]

theorem append {h : List E} {event : E} (before : (Safe (E := E)) h) (positive : Inv (EntryFormat.before event)) (valid : EntryFormat.valid event) : (Safe (E := E)) (h ++ [event]) := by
  intro other member
  rcases List.mem_append.mp member with old | added
  · exact before other old
  · simpa using List.mem_singleton.mp added ▸ And.intro positive valid

theorem lift (action : WG.M α) (preserved : Preserves Inv action) : Observed (E := E) (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
    (fun _ w a result v b hi run => ⟨hi.1,
      (hoare_iff_run_ambient _ _ _).mp preserved w a result v b hi.2 run⟩)

theorem ambient (action : AmbientM α) : Observed (E := E) (liftWGPrefix (monadLift action)) :=
  lift _ (hoare_liftAmbient action Inv)

theorem same_world {action : WG.M α} (same : SameView id action) : Observed (E := E) (liftWGPrefix action) :=
  lift _ (world same)

theorem pure (x : α) : Observed (E := E) (pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

theorem loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → WGPrefix E (ForInStep β))
    (hg : ∀ x b, Observed (E := E) (g x b)) : Observed (E := E) (forIn xs b g) :=
  StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => StateInv (E := E) h w) (Safe (E := E))
    (fun _ _ _ _ hi => hi.1) hg

theorem receipt (action : WG.M α) (record : WGRunWitness α → E)
    (entry : ∀ r, EntryFormat.before (record r) = r.before)
    (valid : ∀ r, r.Valid action → EntryFormat.valid (record r)) (preserved : Preserves Inv action) :
    Observed (E := E) (receiptWGObserved (liftWGPrefix action) record) := by
  intro w a h hi
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix action) record w a h
  rw [runWGPrefix_lift] at equation
  change runStatePrefix (receiptWGObserved (liftWGPrefix action) record) w a h = _ at equation
  unfold runStatePrefix at equation
  rw [equation]
  cases run : (action.run w).run a with
  | error stop => exact ⟨[],by simp,hi.1,trivial⟩
  | ok out =>
    rcases out with ⟨⟨result,v⟩,b⟩
    let r : WGRunWitness α := ⟨result,w,v,a,b⟩
    have history := append hi.1 (event := record r) (by simpa only [entry] using hi.2) (valid r run)
    exact ⟨_,rfl,history,history,(hoare_iff_run_ambient _ _ _).mp preserved w a result v b hi.2 run⟩

theorem initiation_observed (msg : Key) : Observed (E := E) (EntrySource.consumeInitiation msg) :=
  receipt _ _ (fun _ => EntryFormat.exchange_before _) (fun _ valid => EntryFormat.exchange_valid _ valid) (initiation msg)

theorem response_observed (msg : Key) : Observed (E := E) (EntrySource.consumeResponse msg) :=
  receipt _ _ (fun _ => EntryFormat.exchange_before _) (fun _ valid => EntryFormat.exchange_valid _ valid) (response msg)

theorem create_initiation_observed (pid : PeerId) : Observed (E := E) (EntrySource.createInitiation pid) :=
  receipt _ _ (fun _ => EntryFormat.exchange_before _) (fun _ valid => EntryFormat.exchange_valid _ valid) (create_initiation pid)

theorem create_response_observed (pid : PeerId) : Observed (E := E) (EntrySource.createResponse pid) :=
  receipt _ _ (fun _ => EntryFormat.exchange_before _) (fun _ valid => EntryFormat.exchange_valid _ valid) (create_response pid)

theorem session_observed (pid : PeerId) : Observed (E := E) (EntrySource.session pid) :=
  receipt _ _ (fun _ => EntryFormat.exchange_before _) (fun _ valid => EntryFormat.exchange_valid _ valid) (session pid)

theorem cookie_observed (msg : Key) : Observed (E := E) (EntrySource.cookie msg : WGPrefix E Unit) := by
  unfold EntrySource.cookie
  cases choice : EntryFormat.cookie (E := E) with
  | none => exact lift _ (cookie_consume msg)
  | some record =>
    exact receipt _ _ (fun r => EntryFormat.cookie_before record choice ⟨msg,r⟩)
      (fun r valid => EntryFormat.cookie_valid record choice ⟨msg,r⟩ valid) (cookie_consume msg)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
