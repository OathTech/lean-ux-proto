import Leanux.Proofs.WG.Noise.DriverTagTransmitFrames

set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.DriverTags.Transmit
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do

/-! Source: instantiate the existing literal transmit factor. Negative errno
returns and the final peer release remain original; the result only retains
the tags of surviving peers. -/
theorem native (entry : TagMap) (family addr : Nat)
    (packets : List Packet) (mtu : Nat) :
    Preserves (Silent.Retained entry) (wgXmit family addr packets mtu) := by
  let P := Silent.Retained entry
  have getPeerRule (pid : PeerId) : Preserves P (getPeer pid) :=
    (getPeer_frame pid).wp (TagsRetained entry)
  have lookup : Preserves P (lookupDst family addr) :=
    (lookupDst_tag_frame family addr).wp (TagsRetained entry)
  have trim (pid : PeerId) : Preserves P (xmitTrim pid) :=
    (xmitTrim_tag_variant pid).wp (TagsRetained entry)
  have splice (pid : PeerId) (packets : List Packet) : Preserves P (xmitSplice pid packets) :=
    (xmitSplice_tag_variant pid packets).wp (TagsRetained entry)
  have stage (pid : PeerId) : Preserves P (sendStagedPackets pid) :=
    Configuration.staged_preserves pid entry
  have pay (pid : Option PeerId) : Preserves P (WG.peerPut pid) := Silent.peerPut entry pid
  have loopback (sites : List HiddenSite) (raised : Bool) :
      Preserves P (loopbackSend sites raised) :=
    (store_frame (loopbackSend_kernel sites raised)).wp (TagsRetained entry)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
    (store_frame (liftRouting_sameWGStore a)).wp (TagsRetained entry)
  have errors : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors+1}) :=
    (modifyDev_frame (fun d => {d with txErrors := d.txErrors+1})
      (fun _ => rfl)).wp (TagsRetained entry)
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec id P xs init f hf
  rw [wgXmitSource_eq]
  rxstack_preserves_source [wgXmitSource,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getPeerRule,lookup,trim,splice,stage,pay,loopback,ambient,routing,errors,loop]

theorem retained (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (g : WGWorld) (ambient : Ambient) (value : Int) (final : WGWorld) (after : Ambient)
    (run : ((wgXmit family addr packets mtu).run g).run ambient =
      .ok ((value,final),after)) :
    TagsRetained (tagView g) (tagView final) :=
  (hoare_iff_run_ambient _ _ _).mp (native (tagView g) family addr packets mtu)
    g ambient value final after (TagsRetained.refl _) run

end Leanux.Proofs.WG.Noise.DriverTags.Transmit
