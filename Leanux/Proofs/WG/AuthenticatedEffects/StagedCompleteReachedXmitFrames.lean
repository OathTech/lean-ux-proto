import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedXmitSource

/-! Carrier frames for the original pre-transmit native operations. Every
successful prefix keeps the incoming account on the actual returned world;
quietness separately covers histories on stopped prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Xmit
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes Configuration TransmitSecurity CausalJournal CompleteProduct

theorem multicast_checked (family addr : Nat) : Checked (Driver.multicastObserved family addr) := by
  apply product_store
  intro initial
  change Framing.Preserves (fun w : World => productStoreView w = initial) _
  have loop : Framing.Preserves (fun w : World => productStoreView w = initial)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    liftWG_sameProductStore _ (loopbackSend_kernel [] true) initial
  have effects {α : Type} (action : AmbientM α) :
      Framing.Preserves (fun w : World => productStoreView w = initial)
        (monadLift action : Leanux.M α) :=
    productAmbient_spec action _ (fun _ _ before=>before)
  routing_tx_source [Env.xmitMulticastLoop] using [loop,effects]

set_option maxHeartbeats 600000 in
theorem prepare_checked (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Checked (prepare family addr payload opts) := by
  change PrefixPreserves Carrier Safe (prepare family addr payload opts)
  unfold prepare
  repeat' first
    | (traffic_head multicastObserved; exact multicast_checked _ _)
    | (traffic_head routeLookup; exact routing _)
    | (traffic_head neighbourClassify; exact routing _)
    | (traffic_head getWG; exact product_store _ (fun state=>productGetWG_spec (fun s=>s=state)))
    | (traffic_head xmitPackets; exact product_store _ (xmitPackets_sameKernel _ _ _ _))
    | (traffic_head fixtureSend; unfold Env.fixtureSend; exact ambient _)
    | (traffic_head unsupported; exact ambient (AmbientM.unsupported _))
    | with_reducible exact PrefixPreserves.pure carrier_safe _
    | with_reducible apply PrefixPreserves.bind
    | maintenance_intro
    | dsimp only
    | split

theorem prepare_quiet (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    HistoryFrame (fun e : Event=>some e) (prepare family addr payload opts) := by
  unfold prepare Driver.multicastObserved
  repeat' first
    | exact HistoryFrame.lift _ _
    | exact HistoryFrame.pure _ _
    | apply HistoryFrame.bind
    | maintenance_intro
    | split

theorem prepare_history (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts)
    (w : World) (history : List Event) :
    (runPrefix (prepare family addr payload opts) w history).2=history := by
  simpa using prepare_quiet family addr payload opts w history

theorem normal {body : PrefixM Event α} (checked : Checked body)
    (before : Carrier history w) (run : runPrefix body w history=(.ok (value,v),last)) :
    Carrier last v := by
  obtain ⟨_,_,_,kept⟩:=checked w history before
  rw [run] at kept
  exact kept

theorem entered_run (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : World) (history : List Event) :
    runPrefix (entered family addr packets mtu) w history=
      (.ok (history.length,w),history++[.scope (.entered ⟨history.length,.fixture (.transmit family addr packets mtu)⟩)]) := rfl

theorem entered_checked (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Checked (entered family addr packets mtu) := by
  apply CompleteProduct.state
  exact CausalScope.enterState_preserves Event.scope _
    (CompleteAllocatedFixture.scope_safe Safe account_safe)
    (fun event _ _ _ before=>CompleteAllocatedFixture.marker event before)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Xmit
