import Leanux.Proofs.WG.Index.TransmitAmbientRulesSource
import Leanux.Proofs.WG.Index.StackAmbientRulesSource
import Leanux.Proofs.WG.Index.StagingIndexSource
import Leanux.Proofs.WG.Index.TimerCoreSource
import Leanux.Proofs.WG.Noise.PendingStackSource
import Leanux.Proofs.WG.Queues.RxStackProtection
import Leanux.Proofs.WG.Queues.CurrentSlotStack

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TransmitCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem xmitTrim_view {V : Type} (view : WGWorld→V) (pid : PeerId)
    (update : ∀w d p, w.dev=some d→d.peers[pid]?=some p→
      view {w with dev:=some {d with peers:=d.peers.insert pid {p with staged:=p.staged.drop 1}, txDropped:=d.txDropped+1}}=view w) :
    SameView view (xmitTrim pid) := by
  have step : SameView view (do
      let p ← getPeer pid
      if ← branch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS) then
        setPeer pid {p with staged:=p.staged.drop 1}
        modifyDev fun d=>{d with txDropped:=d.txDropped+1}
        pure (ForInStep.yield (PUnit.unit : PUnit.{1}))
      else pure (ForInStep.done (PUnit.unit : PUnit.{1}))) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro g a result v b run
    cases device:g.dev with
    | none =>
      simp [getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident:d.peers[pid]? with
      | none =>
        simp [getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases trim:p.staged.length > MAX_STAGED_PACKETS
        · simp [getPeer,getDev,device,resident,branch,AmbientM.branch,trim,setPeer,modifyDev] at run
          obtain ⟨⟨rfl,rfl⟩,rfl⟩:=run
          simpa only [List.drop_one] using update g d p device resident
        · simp [getPeer,getDev,device,resident,branch,AmbientM.branch,trim] at run
          obtain ⟨⟨rfl,rfl⟩,rfl⟩:=run
          rfl
  intro initial
  change Preserves (fun g=>view g=initial) (xmitTrim pid)
  unfold xmitTrim
  apply preserves_bind
    (hoare_consequence (getPeer_spec pid (fun g=>view g=initial)) (fun _ h=>h) (fun _ _ h=>h.1))
  intro p
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind
    (list_view_spec view (fun s=>s=initial) _ _ _ (fun _ _=>step.wp (fun s=>s=initial)))
  intro _
  exact preserves_pure ()

theorem wgXmit_preserves_source (P : WGWorld→Prop) (family addr : Nat)
    (packets : List WG.Packet) (mtu : Nat)
    (store : ∀{α : Type}, (action : WG.M α)→SameWGStore action→Preserves P action)
    (lookup : Preserves P (lookupDst family addr))
    (trim : ∀pid,Preserves P (xmitTrim pid))
    (splice : ∀pid packets,Preserves P (xmitSplice pid packets))
    (stage : ∀pid,Preserves P (sendStagedPackets pid))
    (pay : ∀peer,Preserves P (peerPut peer))
    (errors : Preserves P (modifyDev fun d=>{d with txErrors:=d.txErrors+1})) :
    Preserves P (wgXmit family addr packets mtu) := by
  apply ReceiveCompletion.Rules.to_native
  apply TransmitAmbientRules.wgXmit_rule
  · intro site value
    exact ReceiveCompletion.Rules.of_native (hoare_liftAmbient (AmbientM.branch site value) P)
  · exact ReceiveCompletion.Rules.of_native lookup
  · intro pid; exact ReceiveCompletion.Rules.of_native (trim pid)
  · intro pid xs; exact ReceiveCompletion.Rules.of_native (splice pid xs)
  · intro pid; exact ReceiveCompletion.Rules.of_native (stage pid)
  · intro peer; exact ReceiveCompletion.Rules.of_native (pay peer)
  · intro sites raised; exact ReceiveCompletion.Rules.of_native
      (store _ (loopbackSend_kernel sites raised))
  · intro src dst; exact ReceiveCompletion.Rules.of_native
      (store _ (liftRouting_sameWGStore (Net.routeOutput4 src dst)))
  · intro dev addr; exact ReceiveCompletion.Rules.of_native
      (store _ (liftRouting_sameWGStore (Net.Fib.inetDevAddrType dev addr)))
  · intro dev; exact ReceiveCompletion.Rules.of_native
      (store _ (liftRouting_sameWGStore (Net.neighbourClassify dev)))
  · intro sites; exact ReceiveCompletion.Rules.of_native
      (hoare_liftAmbient (AmbientM.skipCutSites sites) P)
  · intro site; exact ReceiveCompletion.Rules.of_native
      (hoare_liftAmbient (AmbientM.envOk site) P)
  · exact ReceiveCompletion.Rules.of_native errors


theorem stack_preserves_source (P : World→Prop) (bytes : List UInt8)
    (store : ∀w v,productStoreView v=productStoreView w→P w→P v)
    (send : ∀family addr packets mtu,Preserves P (liftWG (wgXmit family addr packets mtu))) :
    PrefixPreserves (fun (_ : List Empty)=>P) (fun _=>True)
      (PendingStack.stackSource bytes) := by
  have frame {α : Type} (action : Leanux.M α) (same : SameProductStore action) :
      Preserves P action := by
    apply (hoare_iff_run _ _ _).mpr
    intro w value after pre run
    exact store w after ((ProjectedAction.iff_run _ _ _).mp same w value after run) pre
  have routing {α : Type} (action : Net.M α) :
      Preserves P (liftWG (liftRouting action)) :=
    frame _ (liftWG_sameProductStore _ (liftRouting_sameWGStore action))
  have ambient {α : Type} (action : AmbientM α) :
      Preserves P (liftAmbient action) :=
    frame _ (fun state=>productAmbient_spec action
      (fun w=>productStoreView w=state) (fun _ _ hi=>hi))
  apply StackAmbientRules.stack_rule P bytes send
  · intro sites; exact ambient (AmbientM.skipCut sites)
  · intro src dst; exact routing _
  · exact frame _ (fun state=>productGetDev_spec (fun s=>s=state))
  · intro dev; exact routing _
  · intro src dst; exact routing _
  · exact frame _ (fun state=>productGetWG_spec (fun s=>s=state))
  · intro f
    apply frame
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w value after run
    cases run
    rfl
  · intro pkt; exact frame _ (stackReceive6_sameKernel pkt)


end Leanux.Proofs.WG.Index.TransmitCore
