import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastStackFrames

/-! Concrete inner delivery and native IPv4 replies preserve the historical
exclusion carrier, using the existing exact Stack source factors. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues

theorem stack_reply (dst : Nat) (bytes : List UInt8) :
    Preserves (fun w : World => Ready past active w.wg) (Env.Stack.reply4 dst bytes) := by
  let xmit := fun family addr packets mtu =>
    (liftPrefix (liftWG (wgXmit family addr packets mtu)) : PrefixM Unit Int)
  have erased := (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.reply_erases)
    xmit (fun _ _ _ _ => erasesPrefix_lift _) dst bytes
  apply native_of_source _ _ erased
  apply reply4With_preserves (fun _ _ _ => True.intro) (fun _ _ _ same hi => product_transport same hi) xmit
  intro family addr packets mtu
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ _ => True.intro)
  intro h w result v before run
  exact (hoare_iff_run _ _ _).mp (PublicationPoll.native_product (Ready past active) _
    (transmit family addr packets mtu)) w result v before run

theorem stack_receive4 (bytes : List UInt8) :
    Preserves (fun w : World => Ready past active w.wg) (Env.Stack.receive4 bytes) := by
  let reply := fun dst bytes => (liftPrefix (Env.Stack.reply4 dst bytes) : PrefixM Unit Unit)
  apply native_of_source _ _ ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.receive_erases)
    reply (fun _ _ => erasesPrefix_lift _) bytes)
  apply receive4With_preserves (fun _ _ _ => True.intro) (fun _ _ _ same hi => product_transport same hi) reply
  intro dst packet
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ _ => True.intro)
  intro h w result v before run
  exact (hoare_iff_run _ _ _).mp (stack_reply dst packet) w result v before run

theorem deliver_inner (bytes : List UInt8) :
    Preserves (fun w : World => Ready past active w.wg) (Env.deliverInner bytes) := by
  let receive := fun bytes => (liftPrefix (Env.Stack.receive4 bytes) : PrefixM Unit Unit)
  change Preserves (fun w : World => Ready past active w.wg) (Env.Stack.receive bytes)
  apply native_of_source _ _ ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.stack_erases)
    receive (fun _ => erasesPrefix_lift _) bytes)
  apply stackReceiveWith_preserves (fun _ _ _ => True.intro) (fun _ _ _ same hi => product_transport same hi) receive
  intro packet
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ _ => True.intro)
  intro h w result v before run
  exact (hoare_iff_run _ _ _).mp (stack_receive4 packet) w result v before run

theorem stack (packets : List (List UInt8)) :
    Preserves (fun w : World => Ready past active w.wg) (packets.forM Env.deliverInner) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliver_inner bytes) (fun _ => ih)

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
