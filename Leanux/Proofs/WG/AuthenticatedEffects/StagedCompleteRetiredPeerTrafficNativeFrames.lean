import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTrafficEndpointFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterActors

/-! Closed native traffic endpoints. Each account uses the original observer's
actual returned history, and no callback or output-account premise remains. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Traffic
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits DurableHolders

/-- The successful native inject drain empties the exact RX carrier ledger. -/
theorem inject_normal (hi : Inv cs loans h w)
    (run : runPrefix (RxHistory.inject family port msg tos ll dest) w h=(.ok (result,v),k)) :
    ∃ admitted,InjectAccount.Outcome cs admitted family port msg tos ll dest w v h k result ∧
      Inv [] loans k v ∧ result=(msg.length : Int) ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket),v.wg.dev=some d→d.rxSkbs[id]?≠some packet) :=
  RetiredPeer.Traffic.inject_normal (fun initial before=>Outer.actors initial loans before) hi run

theorem flood_normal (hi : Inv cs loans h w)
    (run : runPrefix (RxHistory.flood count port family input) w h=(.ok (result,v),k)) :
    ∃ next,FloodAccount.Outcome cs next count port family input w v h k result ∧ Inv next loans k v :=
  RetiredPeer.Traffic.flood_normal (fun initial before=>Outer.actors initial loans before) hi run

theorem batch_normal (hi : Inv cs loans h w)
    (run : runPrefix (RxHistory.batch entries) w h=(.ok (result,v),k)) :
    ∃ next,BatchAccount.Outcome cs next entries w v h k result ∧ Inv next loans k v :=
  RetiredPeer.Traffic.batch_normal (fun initial before=>Outer.actors initial loans before) hi run

theorem inject_native (hi : Inv cs loans h w)
    (run : (Env.inject family port msg tos ll dest).run w=.ok (result,v)) :
    let k := (runPrefix (RxHistory.inject family port msg tos ll dest) w h).2
    ∃ admitted,InjectAccount.Outcome cs admitted family port msg tos ll dest w v h k result ∧
      Inv [] loans k v ∧ result=(msg.length : Int) ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket),v.wg.dev=some d→d.rxSkbs[id]?≠some packet) :=
  inject_normal hi (Prod.ext ((RxHistory.inject_erases family port msg tos ll dest w h).trans run) rfl)

theorem flood_native (hi : Inv cs loans h w)
    (run : (Env.flood count port family input).run w=.ok (result,v)) :
    let k := (runPrefix (RxHistory.flood count port family input) w h).2
    ∃ next,FloodAccount.Outcome cs next count port family input w v h k result ∧ Inv next loans k v :=
  flood_normal hi (Prod.ext ((RxHistory.flood_erases count port family input w h).trans run) rfl)

theorem batch_native (hi : Inv cs loans h w)
    (run : (Env.batch entries).run w=.ok (result,v)) :
    let k := (runPrefix (RxHistory.batch entries) w h).2
    ∃ next,BatchAccount.Outcome cs next entries w v h k result ∧ Inv next loans k v :=
  batch_normal hi (Prod.ext ((RxHistory.batch_erases entries w h).trans run) rfl)

theorem inject_boundary : Preserves Boundary (Env.inject family port msg tos ll dest) := by
  apply (hoare_iff_run _ _ _).mpr
  rintro w result v ⟨h,cs,hi⟩ run
  obtain ⟨_,_,post,_,_⟩ := inject_native hi run
  exact ⟨_,[],post⟩

theorem flood_boundary : Preserves Boundary (Env.flood count port family input) := by
  apply (hoare_iff_run _ _ _).mpr
  rintro w result v ⟨h,cs,hi⟩ run
  obtain ⟨next,_,post⟩ := flood_native hi run
  exact ⟨_,next,post⟩

theorem batch_boundary : Preserves Boundary (Env.batch entries) := by
  apply (hoare_iff_run _ _ _).mpr
  rintro w result v ⟨h,cs,hi⟩ run
  obtain ⟨next,_,post⟩ := batch_native hi run
  exact ⟨_,next,post⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Traffic
