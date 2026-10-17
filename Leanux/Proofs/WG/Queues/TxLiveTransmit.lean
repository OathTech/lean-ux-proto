import Leanux.Proofs.WG.Queues.TxLiveSend
import Leanux.Proofs.WG.Packets.TxFront

/-! Concrete transmit entry retains the live encryption-ring frontier. The
route, lookup borrow, both splice getters and final payment remain actual. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem store_ready (action : WG.M α) (frame : SameWGStore action) : Preserves Ready action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b run
  have dev : v.dev=w.dev := congrArg WGStoreView.dev same
  simpa only [Ready,Inv,Physical,dev] using hi

private theorem lookup_ready (family addr : Nat) : Preserves Ready (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none=>
    change wgStoreView v=wgStoreView w at borrowed
    have dev : v.dev=w.dev := congrArg WGStoreView.dev borrowed
    simpa only [Ready,Inv,Physical,dev] using hi
  | some pid=>
    obtain ⟨d,p,device,_,_,same⟩ := borrowed
    change w.dev=some d at device
    have endpoint := congrArg WGStoreView.dev same
    change v.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} at endpoint
    simpa only [Ready,Inv,Physical,device,endpoint,Option.some.injEq,forall_eq'] using hi

private theorem trim_ready (pid : PeerId) : Preserves Ready (xmitTrim pid) := by
  unfold xmitTrim
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' live_send_step

private theorem splice_ready (pid : PeerId) (packets : List WG.Packet) :
    Preserves Ready (xmitSplice pid packets) := by
  unfold xmitSplice
  repeat' live_send_step

theorem front (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves Ready (Packets.txFront family addr packets mtu) := by
  have getPeerRule (pid : PeerId) : Preserves Ready (getPeer pid) := by live_send_step
  have pay := peer_put
  have look := lookup_ready family addr
  have trim := trim_ready
  have splice := splice_ready
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves Ready (loopbackSend sites raised) :=
    store_ready _ (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves Ready (monadLift a : WG.M α) :=
    hoare_liftAmbient a Ready
  have routing {α : Type} (a : Net.M α) : Preserves Ready (monadLift a : WG.M α) :=
    store_ready _ (liftRouting_sameWGStore a)
  have errors : Preserves Ready (modifyDev fun d=>{d with txErrors:=d.txErrors+1}) := by live_send_step
  have loop {α β : Type} (xs : List α) (init : β) (f : α→β→WG.M (ForInStep β))
      (hf : ∀x b,Preserves Ready (f x b)) : Preserves Ready (forIn xs init f) :=
    list_view_spec id Ready xs init f hf
  rxstack_preserves_source [Packets.txFront,Packets.txCheck,Packets.txSelect,Packets.txError,
      Packets.txHeaders,Packets.txWalk,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getPeerRule,look,trim,splice,pay,loopback,ambient,routing,errors,loop]

/-- Full native transmit retains both properties on every normal status,
including negative returns; the original nullable payment may erase its peer. -/
theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves Ready (wgXmit family addr packets mtu) := by
  rw [Packets.wgXmit_front_factor]
  apply preserves_bind (front family addr packets mtu)
  intro result
  cases result with
  | error err=>exact preserves_pure err
  | ok pid=>
    unfold Packets.txTail
    exact preserves_bind (send pid) (fun _=>preserves_bind (peer_put (some pid)) (fun _=>preserves_pure 0))

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
