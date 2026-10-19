import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedCarrier
import Leanux.Proofs.WG.Lifetimes.ConfigurationDevice

/-! Native allocation frames used beside packet conservation in configuration.
They retain campaign 1's actual allocation invariant, including fresh slots. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.AllocatedFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity StackOwnership

theorem observed {observer : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix observer native)
    (keeps : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe observer) :
    Preserves Allocated native := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  exact Allocated.native erases keeps before a b run

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves Allocated action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  exact before.store ((ProjectedAction.iff_run_ambient _ _ _).mp same w a value v b run)

theorem configuration {action : WG.M α} (same : SameConfiguration action) : Preserves Allocated action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  obtain ⟨history,allocated⟩ := before
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp same w a value v b run
  exact ⟨history,allocationConfigurationStable history w v
    (congrArg WGOwnedView.toWGStoreView frame) allocated⟩

theorem read (pid : PeerId) : Preserves Allocated (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  obtain ⟨rfl,_,_,_,_⟩ := getPeer_normal pid w v value a b run
  exact before

theorem update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p, (f p).internalId = p.internalId) :
    Preserves Allocated (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,write⟩ := run
  obtain ⟨rfl,rfl,d,device,resident⟩ := getPeer_normal pid w u p a c read
  obtain ⟨history,allocated⟩ := before
  cases value
  have atSlot : (identityView u).1.slots pid = some (f p).internalId := by
    simp only [identityView,Peers.snapshot,device,Option.bind_some,resident,Option.map_some,stamp]
  exact ⟨history,allocated.congr (setPeer_identity pid (f p) _ v _ b atSlot write)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (setPeer_metadata pid (f p)) _ _ () v b write)⟩

theorem public_lookup (key : Key) : Preserves Allocated (pubkeyLookup key) :=
  observed (pubkeyLookupPrefix_erases key) (pubkeyLookupPrefix_preserves_ambient allocationAmbient key)

theorem acquire (pid : PeerId) : Preserves Allocated (peerGet pid) :=
  observed (peerGetMixed_erases pid) (allocationAmbient.peerGet pid)

theorem release (peer : Option PeerId) : Preserves Allocated (peerPut peer) :=
  observed (peerPutMixed_erases peer) (allocationAmbient.peerPut peer)

theorem precompute (pid : PeerId) : Preserves Allocated (precomputeStaticStatic pid) :=
  observed (precomputeStaticStaticMixed_erases pid) (precomputeStaticStaticMixed_allocation pid)

theorem configured (call : ConfigurationCall) : Preserves Allocated call.original :=
  observed call.erases call.allocation

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.AllocatedFrames
