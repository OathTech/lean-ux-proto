import Leanux.Proofs.WG.Packets.PublicationChecks
import Leanux.Proofs.WG.Origins.OwnerWorkers

/-! Owner evidence and packet certificates share the original receive journal.
The generic rules retain the actual stopped prefix as well as normal state. -/
namespace Leanux.Proofs.WG.PublicationJoint
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

def Inv (h : List RxHistory.Event) (w : World) : Prop :=
  OwnerChecks.Inv h w ∧ PublicationChecks.Inv h w

def Safe (h : List RxHistory.Event) : Prop :=
  OwnerChecks.Safe h ∧ PublicationChecks.Safe h

abbrev Preserves (g : RxHistory.Obs α) := PrefixPreserves Inv Safe g

theorem Inv.safe (hi : Inv h w) : Safe h := ⟨hi.1.safe,hi.2.2⟩

/-- Both premises describe this very run, including its error journal. -/
theorem combine (g : RxHistory.Obs α) (owner : OwnerChecks.Preserves g)
    (publication : PublicationChecks.Preserves g) : Preserves g := by
  intro w h hi
  obtain ⟨suffix,appends,ownerSafe,ownerPost⟩ := owner w h hi.1
  obtain ⟨_,_,publicationSafe,publicationPost⟩ := publication w h hi.2
  refine ⟨suffix,appends,⟨ownerSafe,publicationSafe⟩,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out => exact ⟨by simpa only [result] using ownerPost,
      by simpa only [result] using publicationPost⟩

theorem store (h : List RxHistory.Event) (w v : World)
    (eq : productStoreView v = productStoreView w) (hi : Inv h w) : Inv h v := by
  refine ⟨OwnerWorkers.store h w v eq hi.1,?_,hi.2.2⟩
  have dev : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) eq
  apply hi.2.1.transport_cells
  · intro id pkt cell _
    exact ⟨by simpa only [RxDisposition.nativeRxStore,dev] using cell,
      by simp only [packetStamp,dev]⟩
  · exact PublicationFrontier.FrontiersLe.of_eq (by simp only [PublicationFrontier.frontier,dev])
  · intro pid d p hd hp
    exact ⟨d,p,dev.symm.trans hd,hp,rfl⟩

theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) :
    Preserves (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.safe) store frame

theorem quiet (g : RxHistory.Obs α) (a : Leanux.M α)
    (owner : OwnerChecks.Preserves g) (appends : Appends g)
    (erases : ErasesPrefix g a) (frame : HistoryFrame PublicationChecks.sensitive g)
    (preserves : ∀ history, Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) a) :
    Preserves g :=
  combine g owner (PublicationChecks.quiet g a appends erases frame preserves)

/-- A lifetime-only native observer cannot append a consumed event. Its
normal publication transport is supplied for its actual native action. -/
theorem native_mixed (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (owner : OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver g)))
    (erases : ErasesStatePrefix g a)
    (preserves : ∀ history, Framing.Preserves (PublicationFrontier.Inv history) a) :
    Preserves (RxHistory.mixed (liftWGObserver g)) :=
  quiet _ (liftWG a) owner (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases erases))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      PublicationChecks.sensitive (fun _ => rfl) _)
    (fun history => PublicationPoll.native_product _ _ (preserves history))

theorem initial (net bare : Bool) (w : World)
    (hw : wgStoreView w.wg = wgStoreView (Runner.initialWG net bare)) : Inv [] w :=
  ⟨OwnerChecks.initial net bare w hw,PublicationChecks.initial net bare w hw⟩

end Leanux.Proofs.WG.PublicationJoint
