import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTerminalObserved

/-! Forward coverage at the actual packet erase: every completed native free
emits its receipt immediately, before a later reference release can stop. A
failed free has no mutation or emitted terminal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Terminal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues AuthenticatedEffects

private theorem native_free_run (skb : SkbId) (w : World) (d : Device) (packet : DataPacket)
    (device : w.wg.dev = some d) (resident : d.txSkbs[skb]? = some packet)
    (h : List TxDisposition.Event) :
    runPrefix (StagedDisposal.TxSource.native.access (freeTxSkbPrefix skb)) w h =
      (.ok ((),{w with wg := Packets.update w.wg (fun dev => {dev with txSkbs := dev.txSkbs.erase skb})}),
       h ++ [.access (.packet (.read (.inl skb) (packetStamp w.wg skb))),
             .access (.packet (.release (.inl skb) (packetStamp w.wg skb)))]) := by
  apply focusPrefix_suffix TxDisposition.Event.access TxDisposition.accessEvent _ _ _ _
    [.packet (.read (.inl skb) (packetStamp w.wg skb)),
     .packet (.release (.inl skb) (packetStamp w.wg skb))]
  rw [liftWGObserver_run]
  change ((runStatePrefix (freeTxSkbPrefix skb) w.wg w.ambient _).1.map _,
    (runStatePrefix (freeTxSkbPrefix skb) w.wg w.ambient _).2) = _
  rw [freeTxSkbPrefix_run,Packets.getTxSkb_run w.wg w.ambient d skb packet device resident,
    Packets.freeTxSkb_run w.wg w.ambient d skb packet device resident]
  rfl

/-- The receipt follows the same two native lifetime accesses. Its position
is before the caller's remaining keypair/peer release or loop continuation. -/
theorem freeObserved_native (encode : TxDisposition.Event → E)
    (decode : E → Option TxDisposition.Event) (record : Receipt → E)
    (reason : Reason) (skb : SkbId) (w v : World) (h : List E)
    (run : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    runPrefix (freeObserved encode decode record reason skb) w h =
      (.ok ((),v), h ++
        [encode (.access (.packet (.read (.inl skb) (packetStamp w.wg skb)))),
         encode (.access (.packet (.release (.inl skb) (packetStamp w.wg skb))))] ++
        [record ⟨reason,skb,⟨(),w,v⟩⟩]) := by
  obtain ⟨d,packet,device,resident,rfl⟩ := native_free skb w v run
  apply observed_completed
  exact focusPrefix_suffix encode decode _ _ _ _ _ (native_free_run skb w d packet device resident _)

theorem freeObserved_failed (encode : TxDisposition.Event → E)
    (decode : E → Option TxDisposition.Event) (record : Receipt → E)
    (reason : Reason) (skb : SkbId) (w : World) (h : List E) (stop : Stop)
    (run : (liftWG (freeTxSkb skb)).run w = .error stop) :
    runPrefix (freeObserved encode decode record reason skb) w h = (.error stop,h) := by
  cases read : ((getTxSkb skb).run w.wg).run w.ambient with
  | error failed =>
    have raw (history : List LifetimeEvent) :
        runPrefix (liftWGObserver (freeTxSkbPrefix skb)) w history = (.error failed,history) := by
      rw [liftWGObserver_run]
      change ((runStatePrefix (freeTxSkbPrefix skb) w.wg w.ambient history).1.map _,
        (runStatePrefix (freeTxSkbPrefix skb) w.wg w.ambient history).2) = _
      rw [freeTxSkbPrefix_run,read]
      rfl
    have native (history : List TxDisposition.Event) :
        runPrefix (StagedDisposal.TxSource.native.access (freeTxSkbPrefix skb)) w history =
          (.error failed,history) := by
      simpa only [StagedDisposal.TxSource.native,TxDisposition.nativeAccess,TxDisposition.access,
        List.map_nil,List.append_nil] using
        focusPrefix_suffix TxDisposition.Event.access TxDisposition.accessEvent _ w history
          (.error failed) [] (by simpa only [List.append_nil] using raw _)
    have focused : runPrefix
        (focusPrefix encode decode (StagedDisposal.TxSource.native.access (freeTxSkbPrefix skb))) w h =
          (.error failed,h) := by
      simpa only [List.map_nil,List.append_nil] using
        focusPrefix_suffix encode decode _ w h (.error failed) []
          (by simpa only [List.append_nil] using native _)
    have actual := (TxDisposition.nativeAccess_erases (freeTxSkbPrefix_erases skb)) w []
    change (runPrefix (StagedDisposal.TxSource.native.access (freeTxSkbPrefix skb)) w []).1 = _ at actual
    rw [native] at actual
    have same : failed = stop := by simpa only [run,Except.error.injEq] using actual
    subst stop
    exact observed_stopped record _ reason skb w h h failed focused
  | ok out =>
    rcases out with ⟨⟨packet,v⟩,ambient⟩
    obtain ⟨_,_,d,device,resident⟩ := Packets.getTxSkb_current skb w.wg v packet w.ambient ambient read
    rw [liftWG_run,Packets.freeTxSkb_run w.wg w.ambient d skb packet device resident] at run
    cases run

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Terminal
