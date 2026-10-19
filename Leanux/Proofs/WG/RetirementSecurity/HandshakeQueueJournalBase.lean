import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueWorker
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueCallbacks
import Leanux.Proofs.WG.RetirementSecurity.DriverOwnership
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter
import Leanux.Proofs.WG.TransmitSecurity.DriverOuterProjection

/-! A joint physical-input and history carrier for the existing shared driver.
Only the handshake history contract is replaced by a neutral callback in the
history-only helper; its actual worker contract must use the checked ring pop.
Exact native projections supply state facts, never internal event chronology. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity

abbrev StateSafe (Valid : List UInt8 → Prop) (Safe : List E → Prop) (g : WGPrefix E α) :=
  StatePrefixPreserves (StateInv Valid Safe) Safe g
abbrev ProductInv (Valid : List UInt8 → Prop) (Safe : List E → Prop) (h : List E) (w : World) :=
  Inv Valid w.wg ∧ Safe h
abbrev ProductSafe (Valid : List UInt8 → Prop) (Safe : List E → Prop) (g : PrefixM E α) :=
  PrefixPreserves (ProductInv Valid Safe) Safe g

def quietHooks (hooks : Driver.Hooks E) : Driver.Hooks E :=
  {hooks with handshake := fun _ _=>pure false}

structure Contracts (Valid : List UInt8 → Prop) (Safe : List E → Prop)
    (hooks : Driver.Hooks E) (ρ : E → Option Nonce.Allocation) : Prop where
  quiet : Driver.ActorHistorySafe Safe (quietHooks hooks)
  projects : Driver.HooksProjects ρ hooks Driver.nonceHooks
  handshake : StateSafe Valid Safe (Driver.handshakeObserved hooks)

theorem checked_state {P : WGWorld → Prop} {Safe : List E → Prop} {g : WGPrefix E α}
    (history : Driver.StateHistorySafe Safe g)
    (native : ∀w a h result v b,P w→(runWGPrefix g w a h).1=.ok ((result,v),b)→P v) :
    StatePrefixPreserves (fun h w _=>P w ∧ Safe h) Safe g := by
  intro w a h before
  obtain ⟨suffix,extension,safe,_⟩:=history w a h before.2
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix (g.run w) a h).1 with
  | error stop=>trivial
  | ok output=>exact ⟨native w a h output.1.1 output.1.2 output.2 before.1 result,safe⟩

theorem checked_product {P : World → Prop} {Safe : List E → Prop} {g : PrefixM E α}
    (history : Driver.ProductHistorySafe Safe g)
    (native : ∀w h result v,P w→(runPrefix g w h).1=.ok (result,v)→P v) :
    PrefixPreserves (fun h w=>P w ∧ Safe h) Safe g := by
  intro w h before
  obtain ⟨suffix,extension,safe,_⟩:=history w h before.2
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop=>trivial
  | ok output=>exact ⟨native w h output.1 output.2 before.1 result,safe⟩

theorem state_native {Valid : List UInt8 → Prop} {Safe : List E → Prop}
    {ρ : E → Option F} {g : WGPrefix E α} {reference : WGPrefix F α} {action : WG.M α}
    (history : Driver.StateHistorySafe Safe g) (projects : StateProjectsPrefix ρ id g reference)
    (erases : ErasesStatePrefix reference action) (keeps : Preserves (Inv Valid) action) :
    StateSafe Valid Safe g :=
  checked_state history (fun w a h result v b before run=>
    (hoare_iff_run_ambient _ _ _).mp keeps w a result v b before
      (DriverOwnership.state_native projects erases w v a b h run))

theorem product_frame {Valid : List UInt8 → Prop} {action : Leanux.M α}
    (same : SameView HandshakeLengths.productView action) : Preserves (fun w : World=>Inv Valid w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have eq := (ProjectedAction.iff_run _ _ _).mp same w result v run
  exact transport eq before

theorem product_native {Valid : List UInt8 → Prop} {Safe : List E → Prop}
    {ρ : E → Option F} {g : PrefixM E α} {reference : PrefixM F α} {action : Leanux.M α}
    (history : Driver.ProductHistorySafe Safe g) (projects : ProjectsPrefix ρ id g reference)
    (erases : ErasesPrefix reference action) (keeps : Preserves (fun w : World=>Inv Valid w.wg) action) :
    ProductSafe Valid Safe g :=
  checked_product history (fun w h result v before run=>
    (hoare_iff_run _ _ _).mp keeps w result v before
      (DriverOwnership.product_native projects erases w v h run))

theorem product_lift (Valid : List UInt8 → Prop) (Safe : List E → Prop)
    (action : Leanux.M α) (keeps : Preserves (fun w : World=>Inv Valid w.wg) action) :
    ProductSafe Valid Safe (liftPrefix action) :=
  checked_product (Driver.History.product_lift action) (fun w h result v before run=>
    (hoare_iff_run _ _ _).mp keeps w result v before (by simpa only [runPrefix_lift] using run))

theorem state_product {g : WGPrefix E α} (keeps : StateSafe Valid Safe g) :
    ProductSafe Valid Safe (liftWGObserver g) := keeps.liftWGObserver

theorem product_ambient (Valid : List UInt8 → Prop) (Safe : List E → Prop) (action : AmbientM α) :
    ProductSafe Valid Safe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_lift Valid Safe _ (productAmbient_spec action _ (fun _ _ before=>before))

theorem product_pure (Valid : List UInt8 → Prop) (Safe : List E → Prop) (value : α) :
    ProductSafe Valid Safe (pure value) := PrefixPreserves.pure (fun _ _ before=>before.2) value

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
