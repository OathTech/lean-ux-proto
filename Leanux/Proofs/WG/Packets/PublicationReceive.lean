import Leanux.Proofs.WG.Packets.PublicationIngress
import Leanux.Proofs.WG.Origins.OwnerReceive

/-! Actual UDP receive and its existing lifetime journal carry publication
anchors and the peer frontier. No initialized history is assumed. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

private theorem nextCpu (history : List RxHistory.Event) :
    Preserves (Inv history) cpumaskNextOnline := by
  unfold cpumaskNextOnline
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head getDev; exact store_preserves getDev_sameWGStore history)
    | (allocation_release_head modifyDev
       apply modifyDev_preserves
       all_goals intros; rfl)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv history))
    | allocation_release_step

theorem packetReceive_preserves (msg : List UInt8) (src : SkbSource)
    (history : List RxHistory.Event) : Preserves (Inv history) (WG.packetReceive msg src) := by
  unfold WG.packetReceive
  simp (config := {zeta := false}) only [branch,queueDeviceWork,unsupported,invariant]
  repeat' first
    | (allocation_release_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (Inv history))
    | (allocation_release_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (Inv history))
    | (allocation_release_head consumeData; exact consumeData_preserves _ _ _ history)
    | (allocation_release_head getDev; exact store_preserves getDev_sameWGStore history)
    | (allocation_release_head modifyDev
       apply modifyDev_preserves
       all_goals intros; rfl)
    | (allocation_release_head cpumaskNextOnline; exact nextCpu history)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv history))
    | allocation_release_step

theorem wgReceive_preserves (msg : List UInt8) (src : SkbSource)
    (history : List RxHistory.Event) : Preserves (Inv history) (WG.wgReceive msg src) := by
  unfold WG.wgReceive
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (allocation_release_head WG.packetReceive; exact packetReceive_preserves _ _ history)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv history))
    | allocation_release_step

/-- The same actual observer supplies the normal native endpoint and the
appended suffix. A Stop keeps its checked prefix without inventing an endpoint. -/
theorem observed_native {α : Type} (observer : RxHistory.Obs α) (action : WG.M α)
    (erases : ErasesPrefix observer (liftWG action))
    (checked : OwnerChecks.Preserves observer)
    (source : ∀ history, Preserves (Inv history) action) :
    PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ Inv h w.wg) OwnerChecks.Safe observer := by
  intro w h hi
  obtain ⟨suffix,appends,safe,post⟩ := checked w h hi.1
  refine ⟨suffix,appends,safe,?_⟩
  cases run : runPrefix observer w h with
  | mk result journal =>
    cases result with
    | error stop => trivial
    | ok out =>
      rcases out with ⟨value,v⟩
      simp only [run] at post appends ⊢
      have native := (erases w h).symm.trans (congrArg Prod.fst run)
      rw [liftWG_run] at native
      cases actual : (action.run w.wg).run w.ambient with
      | error stop => simp [actual,Except.map] at native
      | ok endpoint =>
        rcases endpoint with ⟨⟨x,u⟩,ambient⟩
        simp only [actual,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
        obtain ⟨rfl,rfl⟩ := native
        have kept := (hoare_iff_run_ambient _ _ _).mp (source h)
          w.wg w.ambient x u ambient hi.2 actual
        exact ⟨post,appends ▸ kept.append suffix⟩

theorem consumeData_checked (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ Inv h w.wg) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (consumeDataPrefix msg src ds))) :=
  observed_native _ _ (RxHistory.mixed_erases (liftWGObserver_erases (consumeDataPrefix_erases msg src ds)))
    (OwnerChecks.consumeData msg src ds) (consumeData_preserves msg src ds)

theorem packetReceive_checked (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ Inv h w.wg) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (packetReceivePrefix msg src))) :=
  observed_native _ _ (RxHistory.mixed_erases (liftWGObserver_erases (packetReceivePrefix_erases msg src)))
    (OwnerReceive.packetReceive_checked msg src) (packetReceive_preserves msg src)

theorem wgReceive_checked (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ Inv h w.wg) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  observed_native _ _ (RxHistory.mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases msg src)))
    (OwnerReceive.wgReceive_checked msg src) (wgReceive_preserves msg src)

end Leanux.Proofs.WG.PublicationFrontier
