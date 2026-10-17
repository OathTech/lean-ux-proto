import Leanux.Proofs.WG.Queues.TxLiveTransmit
import Leanux.Proofs.WG.Lifetimes.StackSource

/-! The existing Stack callback factors carry the live ring bound through
native IPv4 replies and the actual delivery callback. No new observer is defined. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem reply_erases {E : Type}
    (xmit : Nat→Nat→List WG.Packet→Nat→PrefixM E Int)
    (erase : ∀family addr packets mtu,ErasesPrefix (xmit family addr packets mtu)
      (liftWG (wgXmit family addr packets mtu))) (dst : Nat) (bytes : List UInt8) :
    ErasesPrefix (reply4With xmit dst bytes) (Leanux.Env.Stack.reply4 dst bytes) := by
  unfold reply4With Leanux.Env.Stack.reply4
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | exact erase _ _ _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | apply erasesPrefix_ite
    | maintenance_intro
    | dsimp only
    | split

private theorem receive_erases {E : Type}
    (reply : Nat→List UInt8→PrefixM E Unit)
    (erase : ∀dst bytes,ErasesPrefix (reply dst bytes) (Leanux.Env.Stack.reply4 dst bytes))
    (pkt : List UInt8) : ErasesPrefix (receive4With reply pkt) (Leanux.Env.Stack.receive4 pkt) := by
  unfold receive4With Leanux.Env.Stack.receive4
  repeat' first
    | with_reducible exact erase _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible exact erasesPrefix_lift_failure_bind (Leanux.Env.Stack.excluded _) (stackExcluded_failure _) _ _
    | with_reducible exact erasesPrefix_lift_failure_bind (invariant _) (fun _=>⟨_,rfl⟩) _ _
    | with_reducible exact erasesPrefix_lift_failure_bind (unsupported _) (fun _=>⟨_,rfl⟩) _ _
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | maintenance_intro
    | dsimp only
    | split
  all_goals exact erasesPrefix_lift _

private theorem stack_erases {E : Type} (receive : List UInt8→PrefixM E Unit)
    (erase : ∀pkt,ErasesPrefix (receive pkt) (Leanux.Env.Stack.receive4 pkt)) (pkt : List UInt8) :
    ErasesPrefix (stackReceiveWith receive pkt) (Leanux.Env.Stack.receive pkt) := by
  unfold stackReceiveWith Leanux.Env.Stack.receive
  dsimp only
  split
  · exact erase pkt
  · split <;> exact erasesPrefix_lift _

private theorem product_transport (same : productStoreView v=productStoreView w)
    (hi : Ready w.wg) : Ready v.wg := by
  have device : v.wg.dev=w.wg.dev := congrArg (fun s : ProductStore43=>s.2.2.2.dev) same
  simpa only [Ready,Inv,Physical,device] using hi

private theorem native_of_source {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (erase : ErasesPrefix g a)
    (keeps : PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True) g) :
    Preserves (fun w : World=>Ready w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  obtain ⟨_,_,_,out⟩ := keeps w [] hi
  have erased := erase w []
  rw [run] at erased
  simpa only [erased] using out

/-- All original route/MTU/classification guards precede the actual transmit. -/
theorem stack_reply (dst : Nat) (bytes : List UInt8) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.Env.Stack.reply4 dst bytes) := by
  let xmit := fun family addr packets mtu=>(liftPrefix (liftWG (wgXmit family addr packets mtu)) : PrefixM Unit Int)
  have erases := reply_erases xmit (fun _ _ _ _=>erasesPrefix_lift _) dst bytes
  apply native_of_source _ _ erases
  apply reply4With_preserves (fun _ _ _=>True.intro) (fun _ _ _ same hi=>product_transport same hi) xmit
  intro family addr packets mtu
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ _=>True.intro)
  intro h w result v hi run
  exact (hoare_iff_run _ _ _).mp (PublicationPoll.native_product Ready _ (transmit family addr packets mtu))
    w result v hi run

/-- The existing IPv4 source handles its actual excluded rows, reply or delivery. -/
theorem stack_receive4 (bytes : List UInt8) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.Env.Stack.receive4 bytes) := by
  let reply := fun dst bytes=>(liftPrefix (Leanux.Env.Stack.reply4 dst bytes) : PrefixM Unit Unit)
  apply native_of_source _ _ (receive_erases reply (fun _ _=>erasesPrefix_lift _) bytes)
  apply receive4With_preserves (fun _ _ _=>True.intro) (fun _ _ _ same hi=>product_transport same hi) reply
  intro dst packet
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ _=>True.intro)
  intro h w result v hi run
  exact (hoare_iff_run _ _ _).mp (stack_reply dst packet) w result v hi run

/-- Actual inner delivery, including the IPv4 TCP reply that re-enters transmit. -/
theorem deliver_inner (bytes : List UInt8) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.Env.deliverInner bytes) := by
  let receive := fun bytes=>(liftPrefix (Leanux.Env.Stack.receive4 bytes) : PrefixM Unit Unit)
  change Preserves (fun w : World=>Ready w.wg) (Leanux.Env.Stack.receive bytes)
  apply native_of_source _ _ (stack_erases receive (fun _=>erasesPrefix_lift _) bytes)
  apply stackReceiveWith_preserves (fun _ _ _=>True.intro) (fun _ _ _ same hi=>product_transport same hi) receive
  intro packet
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ _=>True.intro)
  intro h w result v hi run
  exact (hoare_iff_run _ _ _).mp (stack_receive4 packet) w result v hi run

theorem stack (packets : List (List UInt8)) :
    Preserves (fun w : World=>Ready w.wg) (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil=>exact preserves_pure _
  | cons bytes rest ih=>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliver_inner bytes) (fun _=>ih)

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
