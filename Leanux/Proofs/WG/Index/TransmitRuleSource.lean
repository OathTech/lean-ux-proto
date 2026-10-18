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
  have getPeerRule (pid : PeerId) : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_spec pid P) (fun _ h=>h) (fun _ _ h=>h.1)
  have loopback (sites : List HiddenSite) (raised : Bool) :
      Preserves P (loopbackSend sites raised) := store _ (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
    store _ (liftRouting_sameWGStore a)
  have loop {α β : Type} (xs : List α) (init : β) (f : α→β→WG.M (ForInStep β))
      (hf : ∀x b,Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec id P xs init f hf
  rw [wgXmitSource_eq]
  rxstack_preserves_source [wgXmitSource,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getPeerRule,lookup,trim,splice,stage,pay,loopback,ambient,routing,errors,loop]

theorem stack_preserves_source (P : World→Prop) (bytes : List UInt8)
    (store : ∀w v,productStoreView v=productStoreView w→P w→P v)
    (send : ∀family addr packets mtu,Preserves P (liftWG (wgXmit family addr packets mtu))) :
    PrefixPreserves (fun (_ : List Empty)=>P) (fun _=>True)
      (PendingStack.stackSource bytes) := by
  have safe : ∀(_ : List Empty) w,P w→True := fun _ _ _=>True.intro
  unfold PendingStack.stackSource
  apply stackReceiveWith_preserves safe (fun _=>store)
  intro packet
  apply receive4With_preserves safe (fun _=>store)
  intro dst packet
  apply reply4With_preserves safe (fun _=>store)
  intro family addr packets mtu
  unfold PendingStack.transmit
  apply PrefixEnsures.lift (Q:=fun _ _=>P) _ safe
  intro _ w result v pre run
  exact (hoare_iff_run _ _ _).mp (send family addr packets mtu) w result v pre run

end Leanux.Proofs.WG.Index.TransmitCore
