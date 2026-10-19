import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialBoundedFrames
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialHistory
import Leanux.Proofs.WG.AuthenticatedEffects.TransportJournalBase

/-! The joint RX carrier belongs to one actual shared journal. Successful
returns retain the bounded packet material; stopped prefixes retain every
replay and confirmation certificate already emitted. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder TransmitSecurity

def Safe (h : List Journal.Event) : Prop :=
  Replay.Safe Journal.origin? Journal.replay? h ∧ Confirmation.Safe h

def Carrier (h : List Journal.Event) (w : WGWorld) : Prop :=
  Bounded (h.filterMap Journal.origin?) w ∧ Safe h

abbrev StateSafe (g : WGPrefix Journal.Event α) :=
  StatePrefixPreserves (fun h w _ => Carrier h w) Safe g

abbrev ProductSafe (g : PrefixM Journal.Event α) :=
  PrefixPreserves (fun h w => Carrier h w.wg) Safe g

theorem Safe.empty : Safe [] := by
  refine ⟨?_,Confirmation.Safe.empty⟩
  intro pre event post position
  have length := congrArg List.length position
  simp only [List.length_nil,List.length_append,List.length_cons] at length
  omega

theorem initial (net bare : Bool) : Carrier [] (Runner.initialWG net bare) :=
  ⟨bounded_initial net bare,Safe.empty⟩

theorem Carrier.replay (before : Carrier h w.wg) : Replay.Inv Journal.origin? Journal.replay? h w :=
  ⟨before.1.1,before.2.1⟩

def Quiet (event : Journal.Event) : Prop := Journal.replay? event = none ∧
  ∀ pid kid r, Journal.responder? event ≠ some (.confirmed pid kid r)

theorem Safe.quiet (before : Safe h) (quiet : ∀ e ∈ suffix, Quiet e) : Safe (h ++ suffix) := by
  refine ⟨before.1.quiet ?_,before.2.quiet (fun e member => (quiet e member).2)⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r member
  obtain ⟨e,member,found⟩ := List.mem_filterMap.mp member
  rw [(quiet e member).1] at found
  cases found

theorem bounded_append (before : Bounded h w) : Bounded (h ++ suffix) w :=
  ⟨before.1.append _,before.2⟩

theorem state_pure (x : α) : StateSafe (pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi)

theorem state_native (action : WG.M α) (frame : ∀ h, Preserves (Bounded h) action) :
    StateSafe (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ hi => hi.2) (fun _ w a x v b hi run =>
    ⟨(hoare_iff_run_ambient _ _ _).mp (frame _) w a x v b hi.1 run,hi.2⟩)

theorem state_bind {g : WGPrefix Journal.Event α} {f : α → WGPrefix Journal.Event β}
    (hg : StateSafe g) (hf : ∀ x, StateSafe (f x)) : StateSafe (g >>= f) :=
  StatePrefixEnsures.bind hg hf

theorem state_ite (p : Prop) [Decidable p] {a b : WGPrefix Journal.Event α}
    (ha : p → StateSafe a) (hb : ¬p → StateSafe b) : StateSafe (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem state_forIn (xs : List α) (init : β) (f : α → β → WGPrefix Journal.Event (ForInStep β))
    (hf : ∀ x b, StateSafe (f x b)) : StateSafe (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact state_pure init
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply state_bind (hf x init)
    intro step
    cases step with
    | done b => exact state_pure b
    | yield b => exact ih b

theorem state_range (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → WGPrefix Journal.Event (ForInStep β))
    (hf : ∀ x b, StateSafe (f x b)) : StateSafe (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact state_forIn _ init f hf

theorem state_observed {g : WGPrefix Journal.Event α} {action : WG.M α}
    (history : Driver.StateHistorySafe Safe g) (erase : ErasesStatePrefix g action)
    (frame : ∀ h, Preserves (Bounded h) action) : StateSafe g := by
  intro w a h hi
  obtain ⟨suffix,appended,safe,_⟩ := history w a h hi.2
  refine ⟨suffix,appended,safe,?_⟩
  cases run : (runPrefix (g.run w) a h).1 with
  | error err => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have native := (erase w a h).symm.trans run
    have kept := (hoare_iff_run_ambient _ _ _).mp (frame _) w a value v b hi.1 native
    change Carrier (runPrefix (g.run w) a h).2 v
    rw [appended]
    exact ⟨by rw [List.filterMap_append]; exact bounded_append kept,appended ▸ safe⟩

theorem product_state {g : WGPrefix Journal.Event α} (safe : StateSafe g) :
    ProductSafe (liftWGObserver g) := safe.liftWGObserver

theorem product_native (action : WG.M α) (frame : ∀ h, Preserves (Bounded h) action) :
    ProductSafe (liftPrefix (liftWG action)) := by
  simpa only [liftWGObserver_lift] using product_state (state_native action frame)

theorem product_pure (x : α) : ProductSafe (pure x) := PrefixPreserves.pure (fun _ _ hi => hi.2) x

theorem product_bind {g : PrefixM Journal.Event α} {f : α → PrefixM Journal.Event β}
    (hg : ProductSafe g) (hf : ∀ x, ProductSafe (f x)) : ProductSafe (g >>= f) := hg.bind hf

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
