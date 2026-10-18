import Leanux.Proofs.WG.Index.TransmitCoreFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TransmitCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem wgXmit_rich (family addr : Nat) (packets : List WG.Packet) (mtu : Nat)
    (entry : WGWorld) :
    Ensures (wgXmit family addr packets mtu)
      (StagingRich.Frame entry) (fun _=>StagingRich.Frame entry) := by
  apply (ensures_iff (wgXmit family addr packets mtu) (StagingRich.Frame entry) (fun _=>StagingRich.Frame entry)).mpr
  apply wgXmit_preserves_source
  · intro α action same
    exact (ensures_iff _ _ _).mp (store_rich action same entry)
  · exact (ensures_iff _ _ _).mp (lookupDst_rich family addr entry)
  · intro pid; exact (ensures_iff _ _ _).mp (xmitTrim_rich pid entry)
  · intro pid xs; exact (ensures_iff _ _ _).mp (xmitSplice_rich pid xs entry)
  · intro pid; exact (ensures_iff _ _ _).mp (StagingRich.sendStagedPackets_rich pid entry)
  · intro pid; exact (ensures_iff _ _ _).mp (StagingRich.peerPut_rich entry pid)
  · exact (ensures_iff _ _ _).mp
      (StagingRich.modifyDev_rich entry _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl))

theorem wgXmit_ready (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves TimerCore.Ready (wgXmit family addr packets mtu) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  have closed := wgXmit_closed family addr packets mtu
    (fun pid=>(CurrentSlots.current pre.1).compatible pid) run
  obtain ⟨delta,handoff⟩ := closed.1
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
    (CurrentSlots.wgXmit_preserves family addr packets mtu) w a result v b pre.1 run,
    StagingRich.core_handoff (wgXmit_rich family addr packets mtu w w a result v b
      (StagingRich.refl w) run) handoff pre.2⟩

theorem stack_ready (bytes : List UInt8) :
    Preserves (fun w : World=>TimerCore.Ready w.wg) (Env.deliverInner bytes) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  have preserved := stack_preserves_source (fun w=>TimerCore.Ready w.wg) bytes
    (fun _ _ same=>ready_product_store same)
    (fun family addr packets mtu=>PublicationPoll.native_product _ _
      (wgXmit_ready family addr packets mtu)) w [] pre
  have original := (PendingStack.stackSource_erases bytes w []).trans run
  simpa only [original] using preserved.choose_spec.2.2

theorem stack_packets_ready (packets : List (List UInt8)) :
    Preserves (fun w : World=>TimerCore.Ready w.wg) (packets.forM Env.deliverInner) := by
  induction packets with
  | nil=>exact preserves_pure _
  | cons bytes rest ih=>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (stack_ready bytes) (fun _=>ih)

end Leanux.Proofs.WG.Index.TransmitCore
