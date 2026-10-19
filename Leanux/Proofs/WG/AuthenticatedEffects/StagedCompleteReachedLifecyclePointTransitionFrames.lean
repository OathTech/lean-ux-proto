import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointJoin

/-! Recreation's temporary ifindex is not an allocation epoch. These exact
native cuts retain the same packet ledger without asserting AllocationInv at
setup/newlink interiors. Reset retains already-terminal tickets; it creates no
terminal outcome. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal
open TransmitSecurity.Staged.Obligations

abbrev History := List Event

def Account (h : History) (w : World) : Prop :=
  ∃ledger,CompleteCarrier.Accounted h ledger [] [] w.wg

theorem account_of_carrier (before : CompleteProduct.Carrier h w) : Account h w := before.1

def setupWorld (w : WGWorld) : WGWorld :=
  {w with dev:=some {ifindex:=0,ifname:="wg0",creatingNet:=false,deviceUpdateGen:=0}}

theorem setup_view (w : WGWorld) : linkView (setupWorld w)=setupLink (linkView w) := rfl

theorem setup_run (w : WGWorld) (a : Ambient) :
    (wgSetup.run w).run a=.ok (((),setupWorld w),a) := rfl

private theorem setup_staged (epoch pid stamp : Nat) :
    stagedPackets epoch pid stamp (setupWorld w)=[] := by
  simp [stagedPackets,Staged.stagedAt,setupWorld]

private theorem setup_cells : TxDisposition.txPackets (setupWorld w)=fun _=>none := by
  funext id
  simp [TxDisposition.txPackets,setupWorld]

private theorem setup_bounds : Packets.Inv (setupWorld w) := by
  simp only [Packets.Inv,Packets.snapshot,Packets.deviceStore,setupWorld,Bounded]
  intro i stamp found
  cases i <;> cases found

private theorem setup_coverage : TxCoverage [] (setupWorld w) := by
  intro id packet found
  simp [setup_cells] at found

private theorem setup_inventory : TxInventory [] (setupWorld w) := by
  constructor
  · simp [txLocalItems]
  · intro pid p found; simp [peerAt,setupWorld] at found
  · intro pid p other q found; simp [peerAt,setupWorld] at found
  · intro pid p found; simp [peerAt,setupWorld] at found
  · intro id member; simp [txLocalItems] at member
  · intro pid p found; simp [peerAt,setupWorld] at found

/-- The actual absent-device guard derives that every old ticket is already
terminal before the native setup overwrites the empty device projection. -/
theorem absent_no_pending (before : CompleteCarrier.Accounted h ledger [] [] w)
    (absent : w.dev=none) : Retired.NoPending ledger :=
  Retired.no_pending before.entry (RetiredFrames.absent_staged absent) (RetiredFrames.absent_cells absent)

theorem setup_accounted (before : CompleteCarrier.Accounted h ledger [] [] w)
    (absent : w.dev=none) : CompleteCarrier.Accounted h ledger [] [] (setupWorld w) :=
  ⟨Retired.empty_replacement before.entry (absent_no_pending before absent)
    setup_staged setup_cells setup_bounds setup_coverage setup_inventory,before.complete⟩

theorem fresh_accounted (before : CompleteCarrier.Accounted h ledger [] [] w)
    (absent : w.dev=none) : CompleteCarrier.Accounted h ledger [] [] (freshDeviceWorld w) := by
  have bounds : Packets.Inv (freshDeviceWorld w) := by
    simp only [Packets.Inv,Packets.snapshot,Packets.deviceStore,freshDeviceWorld,Bounded]
    intro i stamp found
    cases i <;> cases found
  exact ⟨Retired.empty_replacement before.entry (absent_no_pending before absent)
    CompleteDeviceCreation.fresh_staged CompleteDeviceCreation.fresh_cells bounds
    CompleteDeviceCreation.fresh_coverage CompleteDeviceCreation.fresh_inventory,before.complete⟩

/-- The same saved creation entry and literal setup projection accompany the
newlink action. Framing never infers this from a final existential account. -/
structure Creating (h : History) (ledger : Ledger) (initial current : WGWorld) : Prop where
  accounted : CompleteCarrier.Accounted h ledger [] [] initial
  absent : initial.dev=none
  setup : linkView current=setupLink (linkView initial)

theorem Creating.account {initial current : WGWorld} (before : Creating h ledger initial current) :
    CompleteCarrier.Accounted h ledger [] [] current :=
  (setup_accounted before.accounted before.absent).same_view
    (CompleteDeviceCreation.link_frame (before.setup.trans (setup_view initial).symm))

/-- Each original normal newlink branch keeps the same terminal ledger,
including early allocation refusal. Stops have no invented returned World. -/
theorem Creating.newlink {initial current : WGWorld} (before : Creating h ledger initial current)
    (performed : (wgNewlink.run current).run a=.ok ((ret,v),b)) :
    CompleteCarrier.Accounted h ledger [] [] v ∧ Retired.NoPending ledger := by
  have endpoint := (hoare_iff_run_ambient _ _ _).mp
    (wgNewlink_endpoint (setupLink (linkView initial))) current a ret v b before.setup performed
  refine ⟨?_,absent_no_pending before.accounted before.absent⟩
  rcases endpoint with ⟨_,same⟩ | ⟨_,fresh⟩
  · exact (setup_accounted before.accounted before.absent).same_view
      (CompleteDeviceCreation.link_frame (same.trans (setup_view initial).symm))
  · exact (fresh_accounted before.accounted before.absent).same_view
      (CompleteDeviceCreation.link_frame (fresh.trans (freshDevice_linkView initial).symm))

/-- At the original destructor guard, source success and the same holder
account jointly discharge every old pending location before erasure. -/
theorem guard_no_pending (before : CompleteRetired.GuardEntry h ledger holders w)
    (performed : (TxWork.Destruct.check.run w).run a=.ok (((),v),b)) :
    v=w ∧ Retired.NoPending ledger :=
  CompleteRetired.checked_no_pending before.accounted before.service
    (CompleteRetired.checked_staged before.service before.funded before.upper before.base
      before.cursor7 before.cursor8 before.positive performed) performed

/-- The literal native erasure is safe only for the same already-settled
ledger; this theorem does not derive a terminal from reset. -/
theorem erase_accounted (before : CompleteCarrier.Accounted h ledger [] [] w)
    (settled : Retired.NoPending ledger)
    (performed : ((_root_.modify fun s : WGWorld=>{s with dev:=none} : WG.M Unit).run w).run a=
      .ok (((),v),b)) : CompleteCarrier.Accounted h ledger [] [] v := by
  cases performed
  exact CompleteRetired.absent_replacement before settled rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
