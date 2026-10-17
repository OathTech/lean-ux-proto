import Leanux.Proofs.WG.Queues.HolderCallbacks
import Leanux.Proofs.WG.Queues.HolderAuxiliary
import Leanux.Proofs.WG.Queues.CurrentSlotStack
import Leanux.Proofs.WG.Origins.OwnerTraffic

/-! The original native transmit retains its exact acquired TX/send delta in
the complete durable account. Its unchanged mixed observer carries the fixed
RX accounting cut, physical ring, owner journal and three-slot invariant. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderXmit
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

/-- Every actual normal transmit status retains all supplied holders and
absorbs the source-attributed durable delta. The stable ledger is independent
of the carrier ledger; no queue membership is interpreted as fresh funding. -/
theorem funded (family addr : Nat) (packets : List WG.Packet) (mtu : Nat)
    {holders : DurableHolders} (hi : holders.Funded cs loans w)
    (hs : StableRx stable w) (a b : Ambient)
    (run : ((wgXmit family addr packets mtu).run w).run a=.ok ((result,v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧
      (holders.absorb delta).Funded cs loans v ∧ StableRx stable v := by
  have transfer := wgXmit_protection family addr packets mtu hi.carriers.keys run
  have passive := (hoare_iff_run_ambient _ _ _).mp
    (PassiveHolders.wgXmit_preserves family addr packets mtu (passiveView w))
    w a result v b rfl run
  obtain ⟨delta,handoff,paid⟩ := hi.transfer transfer.1 transfer.2 passive
  refine ⟨delta,handoff,paid,hs.retains ?_ handoff.rx ?_ ?_⟩
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (RxRing.wgXmit_cell family addr packets mtu) w a result v b run
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (wgXmit_rxQueues family addr packets mtu) w a result v b run
  · exact (hoare_iff_run_ambient _ _ _).mp
      (NapiFrames.wgXmit_preserves family addr packets mtu (NapiFrames.napiView w))
      w a result v b (NapiFrames.refl w) run

/-- The complete native account survives normal errno and success endpoints.
The output account keeps newly acquired holders rather than forgetting them. -/
theorem boundary (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Boundary cs loans) (wgXmit family addr packets mtu) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨holders,hi,hs⟩ := hi
  obtain ⟨delta,_,paid,stable⟩ := funded family addr packets mtu hi hs a b run
  exact ⟨holders.absorb delta,paid,stable⟩

/-- This is the original lifetime-mixed transmit observer. Its audit events
leave the committed RX removal cut unchanged, including reached Stop prefixes. -/
theorem account (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) := by
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.HolderScheduler.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler.mixed)
    _ (liftWG (wgXmit family addr packets mtu))
    (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu))
  · intro cs
    exact HolderEncrypt.lift_boundary (boundary family addr packets mtu)
  · exact sameView_liftWG RxRing.cell RxRing.nativeCell _
      (RxRing.wgXmit_cell family addr packets mtu) (fun _ _ _ same => same)

/-- Owner checks and nullable slots use the same original observer and native
receipt as the complete account. Incoming histories remain arbitrary. -/
theorem mixed (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) := by
  apply HolderAuxiliary.pair
  · exact account initial loans before family addr packets mtu
  · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerTraffic.«0».Leanux.Proofs.WG.OwnerTraffic.transmit)
      family addr packets mtu
  · intro w h hi result v run
    have source := ((RxHistory.mixed_erases
      (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu))) w h).symm.trans run
    have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
      (wgXmit family addr packets mtu) w v result source
    exact (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.wgXmit_preserves family addr packets mtu)
      w.wg w.ambient result v.wg v.ambient hi.2.2 native

/-- The actual product call has exactly the original mixed observer's final
journal on normal return; there is no separately supplied output invariant. -/
theorem normal (family addr : Nat) (packets : List WG.Packet) (mtu : Nat)
    (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : (liftWG (wgXmit family addr packets mtu)).run w=.ok (result,v)) :
    HolderAuxiliary.Inv initial loans before
      (runPrefix (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) w h).2 v := by
  have actual := ((RxHistory.mixed_erases
    (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu))) w h).trans run
  have post := (mixed initial loans before family addr packets mtu w h hi).choose_spec.2.2
  simpa only [actual] using post

end Leanux.Proofs.WG.Queues.RxCredits.HolderXmit
