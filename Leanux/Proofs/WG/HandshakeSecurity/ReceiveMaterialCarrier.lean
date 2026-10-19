import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialAuthentication
import Leanux.Proofs.WG.RetirementSecurity.ReceiveEntryHolders

/-! The C1 allocation companion derives each selected decrypt's numeric bound.
Its existential history is used only for state facts at this exact action;
it supplies no chronology for the receive certificate journal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity AuthenticatedEffects Responder RetirementSecurity
open StackOwnership

abbrev Allocated := StackOwnership.Allocated

def Carrier (h : List TransportDriver.OriginEvent) (w : WGWorld) : Prop := Inv h w ∧ Allocated w

theorem allocated_bounds (before : Allocated w) : KeyBounds w := before.choose_spec.keySlots

theorem carrier_initial (net bare : Bool) : Carrier [] (Runner.initialWG net bare) :=
  ⟨initial net bare,[],allocation_initial net bare _ rfl⟩

/-- Original preparation preserves the allocation companion through the exact
C1 observer; this normal state transfer makes no claim joining event histories. -/
theorem prepare_allocated : Preserves Allocated RxWorkers.prepareSource := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact RetirementSecurity.Allocated.native RxWorkers.prepare_erases RxWorkers.prepare_preserves hi a b run

/-- Native publication and its existing ordered receipt journal preserve both
RX material and independent allocation bounds. Stop retains the emitted prefix;
only normal returns expose a post-state carrier. -/
theorem prepare_carrier :
    StatePrefixPreserves (fun h w _ => Carrier h w) (fun _ => True) RxOrigin.prepare := by
  intro w a h hi
  obtain ⟨suffix,appended⟩ := TransportDriver.native_prepare_appends w a h
  refine ⟨suffix,appended,True.intro,?_⟩
  cases result : (runPrefix (RxOrigin.prepare.run w) a h).1 with
  | error err => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    refine ⟨prepare_normal w v a b h _ value hi.1 (allocated_bounds hi.2) (Prod.ext result rfl),?_⟩
    have native := (RxOrigin.prepare_erases w a h).symm.trans result
    exact (hoare_iff_run_ambient _ _ _).mp prepare_allocated w a value v b hi.2 native

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
