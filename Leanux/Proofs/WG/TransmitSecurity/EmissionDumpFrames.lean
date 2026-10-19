import Leanux.Proofs.WG.AuthenticatedEffects.EmissionNativeFrames
import Leanux.Proofs.Framing.WGDump

/-! Native netlink dump operations preserve the pending sent buffer, including
cursor peer-reference acquisition and release. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EmissionDump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues NetlinkDump AuthenticatedEffects Std.Do

theorem list_spec (P : List SentDatagram → Prop) {α β : Type} (xs : List α) (acc : β)
    (body : α → β → WG.M (ForInStep β))
    (safe : ∀ x b, Preserves (fun w => P w.sent) (body x b)) :
    Preserves (fun w => P w.sent) (forIn xs acc body) := by
  apply list_view_spec id (fun w : WGWorld => P w.sent)
  intro x b
  exact safe x b

theorem range_spec (P : List SentDatagram → Prop) {β : Type} (xs : Std.Legacy.Range) (acc : β)
    (body : Nat → β → WG.M (ForInStep β))
    (safe : ∀ x b, Preserves (fun w => P w.sent) (body x b)) :
    Preserves (fun w => P w.sent) (forIn xs acc body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply list_view_spec id (fun w : WGWorld => P w.sent)
  intro x b
  exact safe x b

theorem get_peer (P : List SentDatagram → Prop) (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    Preserves (fun w => P w.sent) (getPeerDump pid ctx skb) :=
  ((getPeerDump_sameWGWorld pid ctx skb).factor WGWorld.sent).wp P

theorem get_sock (P : List SentDatagram → Prop) (fd : Nat) :
    Preserves (fun w => P w.sent) (getNlSock fd) :=
  ((getNlSock_sameWGWorld fd).factor WGWorld.sent).wp P

theorem set_sock (P : List SentDatagram → Prop) (fd : Nat) (value : NlSock) :
    Preserves (fun w => P w.sent) (setNlSock fd value) := by
  unfold setNlSock
  apply hoare_modify
  intro w hi
  split <;> exact hi

theorem lookup (P : List SentDatagram → Prop) (ref : DeviceRef) :
    Preserves (fun w => P w.sent) (lookupInterface ref) :=
  ((lookupInterface_sameWGWorld ref).factor WGWorld.sent).wp P

theorem coalesced (P : List SentDatagram → Prop) (messages : List NlMessage) :
    Preserves (fun w => P w.sent) (coalesce messages) :=
  ((coalesce_sameWGWorld messages).factor WGWorld.sent).wp P

theorem done (ctx : DumpCtx) : SameView WGWorld.sent (wgGetDeviceDone ctx) := by
  sent_frame [wgGetDeviceDone] using [peerPut_sent_spec]

theorem header (d : Device) (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) :
    SameView WGWorld.sent (deviceDumpHeaderSource d ctx seq skb) := by
  sent_frame [deviceDumpHeaderSource] using []

theorem tail (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    SameView WGWorld.sent (deviceDumpTailSource d ctx skb flags attrs) := by
  sent_frame [deviceDumpTailSource,requireNotPending] using
    [getPeer_sent_spec,get_peer,peerGet_sent_spec,peerPut_sent_spec,list_spec]

theorem chunk (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) :
    SameView WGWorld.sent (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  have deviceFrame : SameView WGWorld.sent getDev := by sent_frame [] using []
  have device : Preserves (fun w : WGWorld => w.sent = initial) getDev := deviceFrame initial
  exact preserves_bind device (fun d => preserves_bind (header d ctx seq skb initial)
    (fun result => tail d ctx result.1 result.2.1 result.2.2 initial))

theorem chunk_spec (P : List SentDatagram → Prop) (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) :
    Preserves (fun w => P w.sent) (wgGetDeviceDump ctx seq skb) := (chunk ctx seq skb).wp P

theorem done_spec (P : List SentDatagram → Prop) (ctx : DumpCtx) :
    Preserves (fun w => P w.sent) (wgGetDeviceDone ctx) := (done ctx).wp P

theorem dump (fd : Nat) : SameView WGWorld.sent (netlinkDump fd) := by
  sent_frame [netlinkDump] using [get_sock,set_sock,chunk_spec,done_spec]

theorem dump_spec (P : List SentDatagram → Prop) (fd : Nat) :
    Preserves (fun w => P w.sent) (netlinkDump fd) := (dump fd).wp P

theorem start (fd : Nat) (ref : DeviceRef) : SameView WGWorld.sent (netlinkDumpStart fd ref) := by
  sent_frame [netlinkDumpStart] using [get_sock,set_sock,lookup,dump_spec]

theorem receive (fd : Nat) : SameView WGWorld.sent (netlinkRecvmsg fd) := by
  sent_frame [netlinkRecvmsg] using [get_sock,set_sock,dump_spec]

theorem start_spec (P : List SentDatagram → Prop) (fd : Nat) (ref : DeviceRef) :
    Preserves (fun w => P w.sent) (netlinkDumpStart fd ref) := (start fd ref).wp P

theorem receive_spec (P : List SentDatagram → Prop) (fd : Nat) :
    Preserves (fun w => P w.sent) (netlinkRecvmsg fd) := (receive fd).wp P

theorem device (ref : DeviceRef) : SameView WGWorld.sent (wgGetDevice ref) := by
  sent_frame [wgGetDevice] using [start_spec,receive_spec,coalesced,list_spec,range_spec]

end Leanux.Proofs.WG.TransmitSecurity.EmissionDump
