import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceSocketFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriverSource

/-! Positive-reference entry certificates on the existing exchange journal.
The observer is unchanged: a completed native receipt retains its real entry
world, and an inner Stop retains every previously certified receipt. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def Safe (history : List Exchange.Event) : Prop :=
  ∀ event ∈ history, Inv event.before

def StateInv (history : List Exchange.Event) (w : WGWorld) : Prop := Safe history ∧ Inv w

abbrev Observed (action : WGPrefix Exchange.Event α) :=
  StatePrefixPreserves (fun h w _ => StateInv h w) Safe action

theorem safe_nil : Safe [] := by simp [Safe]

theorem append (before : Safe h) (positive : Inv event.before) : Safe (h ++ [event]) := by
  intro other member
  rcases List.mem_append.mp member with old | added
  · exact before other old
  · simpa using List.mem_singleton.mp added ▸ positive

theorem lift (action : WG.M α) (preserved : Preserves Inv action) : Observed (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
    (fun _ w a result v b hi run => ⟨hi.1,
      (hoare_iff_run_ambient _ _ _).mp preserved w a result v b hi.2 run⟩)

theorem ambient (action : AmbientM α) : Observed (liftWGPrefix (monadLift action)) :=
  lift _ (hoare_liftAmbient action Inv)

theorem same_world {action : WG.M α} (same : SameView id action) : Observed (liftWGPrefix action) :=
  lift _ (world same)

theorem pure (x : α) : Observed (pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

theorem loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → WGPrefix Exchange.Event (ForInStep β))
    (hg : ∀ x b, Observed (g x b)) : Observed (forIn xs b g) :=
  StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => StateInv h w) Safe
    (fun _ _ _ _ hi => hi.1) hg

theorem receipt (action : WG.M α) (record : WGRunWitness α → Exchange.Event)
    (entry : ∀ r, (record r).before = r.before) (preserved : Preserves Inv action) :
    Observed (receiptWGObserved (liftWGPrefix action) record) := by
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
    have history := append hi.1 (event := record r) (by simpa only [entry] using hi.2)
    exact ⟨_,rfl,history,history,(hoare_iff_run_ambient _ _ _).mp preserved w a result v b hi.2 run⟩

theorem initiation_observed (msg : Key) : Observed (Exchange.consumeInitiation msg) :=
  receipt _ _ (fun _ => rfl) (initiation msg)

theorem response_observed (msg : Key) : Observed (Exchange.consumeResponse msg) :=
  receipt _ _ (fun _ => rfl) (response msg)

theorem create_initiation_observed (pid : PeerId) : Observed (Exchange.createInitiation pid) :=
  receipt _ _ (fun _ => rfl) (create_initiation pid)

theorem create_response_observed (pid : PeerId) : Observed (Exchange.createResponse pid) :=
  receipt _ _ (fun _ => rfl) (create_response pid)

theorem session_observed (pid : PeerId) : Observed (Exchange.session pid) :=
  receipt _ _ (fun _ => rfl) (session pid)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
