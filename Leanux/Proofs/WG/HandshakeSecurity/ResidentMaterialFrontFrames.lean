import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialPollFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverFrontFrames

/-! Native routing and staging-front frames. Lookup borrows a peer but cannot
replace a resident TX packet's key allocation or sending material. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Std.Do
open TransmitSecurity Responder Origins.Retaining
set_option maxHeartbeats 600000

theorem lookup_snapshot (family addr : Nat) : SameView PacketOrigins.snapshot (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    change (PacketOrigins.epoch v, PacketMaterial.view v) = (PacketOrigins.epoch w, PacketMaterial.view w)
    apply Prod.ext
    · simp only [PacketOrigins.epoch,same]
    · funext id
      simp only [PacketMaterial.view,TxDisposition.txPackets,same]
  | some pid =>
    obtain ⟨d,p,device,_,_,after⟩ := borrowed
    change w.dev = some d at device
    have endpoint : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
      congrArg WGStoreView.dev after
    change (PacketOrigins.epoch v, PacketMaterial.view v) = (PacketOrigins.epoch w, PacketMaterial.view w)
    apply Prod.ext
    · simp only [PacketOrigins.epoch,device,endpoint,Option.map_some]
    · funext id
      simp only [PacketMaterial.view,TxDisposition.txPackets,device,endpoint,Option.bind_some]

theorem lookup (family addr : Nat) : Preserves (Inv h) (lookupDst family addr) := by
  apply frame (lookup_snapshot family addr) (core_of_same (pool_of_material (lookupDst_material family addr)))
  intro bound
  apply lower_frame
  exact ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotStack.«0».Leanux.Proofs.WG.CurrentSlots.lookupDst_view)
    family addr).of_factor (fun s => s.map Affiliation.State.nextKey) cursor
      (fun _ => by simp only [cursor,Affiliation.view,Option.map_map,Function.comp_def,Affiliation.state])

theorem trim (pid : PeerId) : Preserves (Inv h) (xmitTrim pid) := by
  unfold xmitTrim
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' resident_staging_step

theorem splice (pid : PeerId) (packets : List WG.Packet) : Preserves (Inv h) (xmitSplice pid packets) := by
  unfold xmitSplice
  repeat' resident_staging_step

theorem front (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Inv h) (Packets.txFront family addr packets mtu) := by
  have getter (pid : PeerId) : Preserves (Inv h) (getPeer pid) := read_peer _
  have pay := peer_put (h := h)
  have look := lookup (h := h) family addr
  have trimming := trim (h := h)
  have splicing := splice (h := h)
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves (Inv h) (loopbackSend sites raised) :=
    store (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a (Inv h)
  have routing {α : Type} (a : Net.M α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    store (liftRouting_sameWGStore a)
  have errors : Preserves (Inv h) (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
    modify_device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves (Inv h) (f x b)) : Preserves (Inv h) (forIn xs init f) :=
    list_view_spec id (Inv h) xs init f hf
  rxstack_preserves_source [Packets.txFront,Packets.txCheck,Packets.txSelect,Packets.txError,
      Packets.txHeaders,Packets.txWalk,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,look,trimming,splicing,pay,loopback,ambient,routing,errors,loop]

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
