import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductScalarSource

/-! The existing three-scalar mask preserves packet accounting, identities
and allocation frontiers. It does not mask any queue or key selection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductScalar
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal RetirementSecurity

theorem packet_view (w : WGWorld) :
    StagedEntry.view {dev:=(envScalarWGView w).dev}=StagedEntry.view w := by
  cases device : w.dev <;>
    simp [funext_iff,StagedEntry.view,envScalarWGView,envScalarDevice,
      wgStoreView,Packets.epoch,Staged.stagedAt,PacketMaterial.view,
      TxDisposition.txPackets,Packets.snapshot,Packets.deviceStore,txQueueContents,
      RxCredits.handoffTxView,device]

theorem carrier_transport (h : List Event) (w v : World)
    (same : envScalarWGView v.wg=envScalarWGView w.wg)
    (before : CompleteProduct.Carrier h w) : CompleteProduct.Carrier h v := by
  obtain ⟨⟨ledger,accounted⟩,history,allocated⟩ := before
  have full : envScalarView {w with wg:=v.wg}=envScalarView w :=
    congrArg (fun s=>(fsStoreView w.fs,w.tasks,(w.seccomp.filters,w.seccomp.nextFilter),s)) same
  have geometry := envScalar_identity_metadata w {w with wg:=v.wg} full
  have packets := congrArg (fun s : WGStoreView=>StagedEntry.view {dev:=s.dev}) same
  rw [packet_view,packet_view] at packets
  exact ⟨⟨ledger,accounted.same_view packets⟩,history,
    allocated.congr (congrArg Prod.fst geometry) (congrArg Prod.snd geometry)⟩

theorem Shape.frame (source : Shape action) : SameView (fun w : World=>envScalarWGView w.wg) action := by
  induction source with
  | pure value => exact SameView.pure _ _
  | stored source => exact source.frame.factor (fun s : WGStoreView=>{s with dev:=s.dev.map envScalarDevice})
  | write update same => exact fun _ => hoare_modify update (fun w before=>(same w).trans before)
  | bind head tail ihHead ihTail => exact SameView.bind ihHead ihTail

theorem Point.view (point : Point source w v) : envScalarWGView v.wg=envScalarWGView w.wg := by
  induction point with
  | entry source => rfl
  | returned source performed => exact (ProjectedAction.iff_run _ _ _).mp source.frame _ _ _ performed
  | stored point => exact congrArg (fun s : WGStoreView=>{s with dev:=s.dev.map envScalarDevice}) point.store
  | left tail point ih => exact ih
  | right head tail leading point ih =>
      exact ih.trans ((ProjectedAction.iff_run _ _ _).mp head.frame _ _ _ leading)

theorem Point.carrier (point : Point source w v) (before : CompleteProduct.Carrier h w) :
    CompleteProduct.Carrier h v := carrier_transport h w v point.view before

theorem Shape.checked (source : Shape action) : CompleteProduct.Checked (liftPrefix action) := by
  apply PrefixEnsures.lift
  · exact CompleteProduct.carrier_safe
  · intro h w value v before performed
    exact (Point.returned source performed).carrier before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductScalar
