import Leanux.Proofs.WG.TransmitSecurity.NonceStackFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceCallers
import Leanux.Proofs.WG.TransmitSecurity.NoncePoll

/-! The actual IPv4 stack reply callback may re-enter transmit. Its exact
observer closes the receive poll's callback contract without assuming silence
or absence of replies. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

private theorem reply_erases {E : Type}
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (erase : ∀ family addr packets mtu, ErasesPrefix (xmit family addr packets mtu)
      (liftWG (wgXmit family addr packets mtu))) (dst : Nat) (bytes : List UInt8) :
    ErasesPrefix (reply4With xmit dst bytes) (Env.Stack.reply4 dst bytes) := by
  unfold reply4With Env.Stack.reply4
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
    (reply : Nat → List UInt8 → PrefixM E Unit)
    (erase : ∀ dst bytes, ErasesPrefix (reply dst bytes) (Env.Stack.reply4 dst bytes))
    (pkt : List UInt8) : ErasesPrefix (receive4With reply pkt) (Env.Stack.receive4 pkt) := by
  unfold receive4With Env.Stack.receive4
  repeat' first
    | with_reducible exact erase _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible exact erasesPrefix_lift_failure_bind (Env.Stack.excluded _) (stackExcluded_failure _) _ _
    | with_reducible exact erasesPrefix_lift_failure_bind (invariant _) (fun _ => ⟨_,rfl⟩) _ _
    | with_reducible exact erasesPrefix_lift_failure_bind (unsupported _) (fun _ => ⟨_,rfl⟩) _ _
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | maintenance_intro
    | dsimp only
    | split
  all_goals exact erasesPrefix_lift _

def stackObserved : List UInt8 → PrefixM Allocation Unit :=
  stackReceiveWith (receive4With (reply4With
    (fun family addr packets mtu => liftWGObserver (transmitObserved family addr packets mtu))))

theorem stackObserved_erases (bytes : List UInt8) :
    ErasesPrefix (stackObserved bytes) (Env.deliverInner bytes) := by
  have reply := reply_erases _ (fun family addr packets mtu =>
    liftWGObserver_erases (transmitObserved_erases family addr packets mtu))
  have receive := receive_erases _ reply
  unfold stackObserved stackReceiveWith Env.deliverInner Env.Stack.receive
  dsimp only
  split
  · exact receive bytes
  · split <;> exact erasesPrefix_lift _

theorem stackObserved_safe (bytes : List UInt8) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (stackObserved bytes) :=
  stackReceiveWith_preserves (fun _ _ hi => hi.nodup) Frames.product_store _
    (fun bytes => receive4With_preserves (fun _ _ hi => hi.nodup) Frames.product_store _
      (fun dst reply => reply4With_preserves (fun _ _ hi => hi.nodup) Frames.product_store _
        (fun family addr packets mtu => (transmitObserved_safe family addr packets mtu).liftWGObserver)
        dst reply) bytes) bytes

def stackFlushObserved (packets : List (List UInt8)) : PrefixM Allocation Unit :=
  packets.forM stackObserved

theorem stackFlushObserved_erases (packets : List (List UInt8)) :
    ErasesPrefix (stackFlushObserved packets) (packets.forM Env.deliverInner) := by
  induction packets with
  | nil => exact erasesPrefix_pure _
  | cons bytes rest ih =>
    simp only [stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact erasesPrefix_bind (stackObserved_erases bytes) (fun _ => ih)

theorem stackFlushObserved_safe (packets : List (List UInt8)) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (stackFlushObserved packets) := by
  induction packets with
  | nil => exact PrefixPreserves.pure (fun _ _ hi => hi.nodup) _
  | cons bytes rest ih =>
    simp only [stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact PrefixPreserves.bind (stackObserved_safe bytes) (fun _ => ih)

def nativePollObserved (pid : PeerId) (budget : Nat) : PrefixM Allocation Nat :=
  pollObserved pid budget stackFlushObserved

theorem nativePollObserved_erases (pid : PeerId) (budget : Nat) :
    ErasesPrefix (nativePollObserved pid budget)
      (rxPoll pid budget (fun packets => packets.forM Env.deliverInner)) :=
  pollObserved_erases pid budget _ _ stackFlushObserved_erases

theorem nativePollObserved_safe (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (nativePollObserved pid budget) :=
  pollObserved_safe pid budget _ stackFlushObserved_safe

end Leanux.Proofs.WG.TransmitSecurity.Nonce
