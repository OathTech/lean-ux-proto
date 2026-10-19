import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPrimitiveKeySource

/-! Full selected-packet ownership is invariant under the actual key store
and index mutations. The cached peer, ordered cohort and native take anchor
are retained independently of the changing key-reference records. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity CausalJournal Staged.Obligations
set_option maxHeartbeats 600000

theorem selected_same_view
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (same : StagedEntry.view v=StagedEntry.view w) :
    CompleteSelected.Ready ledger debts locals generation pid peer position h v b := by
  have held := before.toHeld.views_append (b:=b) [] (by simp)
    (congrArg Prod.fst same) (congrArg (fun x=>x.2.1) same)
    (congrArg (fun x=>x.2.2.1) same)
  have geometry : RetirementSecurity.StagingOccurrences.geometry v=
      RetirementSecurity.StagingOccurrences.geometry w :=
    Prod.ext (congrArg (fun x=>x.2.2.2.1) same) (congrArg (fun x=>x.2.2.2.2.1) same)
  exact ⟨⟨⟨by simpa only [List.append_nil] using held,before.justified,before.links,before.only⟩,
    NativeReady.frame before.native geometry (congrArg (fun x=>x.2.2.2.2.2) same)⟩,
    before.complete,before.nativeAnchor⟩

theorem selected_append
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (suffix : List Event) (allowed : ∀ event∈suffix,HeldFrontier.progress event=true) :
    CompleteSelected.Ready ledger debts locals generation pid peer position (h++suffix) w a := by
  exact ⟨⟨⟨before.toHeld.views_append suffix allowed rfl rfl rfl,
    before.justified.append suffix,before.links.append suffix,before.only⟩,before.native⟩,
    before.complete.append_quiet (fun event member=>CompleteSelected.progress_terminal_quiet (allowed event member)),
    before.nativeAnchor.append suffix⟩

theorem KeyAtom.frame (token : KeyAtom α) : SameView StagedEntry.view token.action := by
  cases token with
  | branch site flag=>exact fun initial=>hoare_liftAmbient (AmbientM.branch site flag) (fun w=>StagedEntry.view w=initial)
  | compare site flag left right=>exact fun initial=>hoare_liftAmbient (AmbientM.branchCmp site flag left right) (fun w=>StagedEntry.view w=initial)
  | read kid=>exact ReceiveFrames.key_read kid
  | write kid key=>exact ReceiveFrames.device _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
  | owner kid=>exact fun initial=>indexOwner_peerDeref_preserves _ _
  | unhash kid=>exact KeyFrames.index _
  | erase kid=>exact ReceiveFrames.device _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
  | failed α message=>exact fun initial=>hoare_liftAmbient (AmbientM.invariant message) (fun w=>StagedEntry.view w=initial)
  | unsupported α message=>exact fun initial=>hoare_liftAmbient (AmbientM.unsupported message) (fun w=>StagedEntry.view w=initial)

theorem KeyShape.frame (shape : KeyShape action) : SameView StagedEntry.view action := by
  induction shape with
  | pure value=>exact SameView.pure _ value
  | atom token=>exact token.frame
  | bind head tail ihHead ihTail=>exact SameView.bind ihHead ihTail

theorem KeyShape.selected (shape : KeyShape action)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (run : (action.run w).run a=.ok ((value,v),b)) :
    CompleteSelected.Ready ledger debts locals generation pid peer position h v b :=
  selected_same_view before ((ProjectedAction.iff_run_ambient _ _ _).mp shape.frame w a value v b run)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
