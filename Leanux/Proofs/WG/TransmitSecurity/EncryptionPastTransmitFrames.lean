import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastReceiveFrames

/-! Routing, peer borrowing, trim and splice precede packet allocation and
preserve historical encryption exclusion on every native errno path. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition RetirementSecurity
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem ready_lookup_dst (family addr : Nat) :
    Preserves (Ready past active) (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at borrowed
    have device := congrArg WGStoreView.dev borrowed
    have epochs := congrArg WGStoreView.netIfindexNext borrowed
    change v.dev = w.dev at device
    change v.netIfindexNext = w.netIfindexNext at epochs
    simpa only [Ready,LiveFrontier.Ready,LiveFrontier.Inv,LiveFrontier.Physical,view,device,epochs] using before
  | some pid =>
    obtain ⟨d,p,device,_,_,same⟩ := borrowed
    change w.dev = some d at device
    have endpoint := congrArg WGStoreView.dev same
    have epochs := congrArg WGStoreView.netIfindexNext same
    change v.netIfindexNext = w.netIfindexNext at epochs
    change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} at endpoint
    simpa only [Ready,LiveFrontier.Ready,LiveFrontier.Inv,LiveFrontier.Physical,view,
      device,endpoint,epochs,Option.map_some,Option.some.injEq,forall_eq'] using before


theorem ready_trim (pid : PeerId) : Preserves (Ready past active) (xmitTrim pid) := by
  unfold xmitTrim
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' encryption_past_receive_step

theorem ready_splice (pid : PeerId) (packets : List WG.Packet) :
    Preserves (Ready past active) (xmitSplice pid packets) := by
  unfold xmitSplice
  repeat' encryption_past_receive_step

theorem ready_front (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Ready past active) (Packets.txFront family addr packets mtu) := by
  let P := Ready past active
  have getter (pid : PeerId) : Preserves P (getPeer pid) := getPeer_preserves _ _
  have pay (peer : Option PeerId) : Preserves P (peerPut peer) :=
    ready_frame (LiveFrontier.peer_put peer) (peer_put peer)
  have lookup := ready_lookup_dst (past := past) (active := active) family addr
  have trim := ready_trim (past := past) (active := active)
  have splice := ready_splice (past := past) (active := active)
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves P (loopbackSend sites raised) :=
    ready_store (loopbackSend_kernel sites raised)
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  have routing {α : Type} (action : Net.M α) : Preserves P (monadLift action : WG.M α) :=
    ready_store (liftRouting_sameWGStore action)
  have errors : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
    ready_modify _ (fun _ => rfl) (fun _ => rfl)
  have loop {α β : Type} (xs : List α) (initial : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs initial f) :=
    list_view_spec id P xs initial f hf
  rxstack_preserves_source [Packets.txFront,Packets.txCheck,Packets.txSelect,Packets.txError,
    Packets.txHeaders,Packets.txWalk,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,pay,lookup,trim,splice,loopback,ambient,routing,errors,loop]

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
