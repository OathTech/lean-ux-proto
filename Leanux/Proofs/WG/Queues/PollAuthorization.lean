import Leanux.Proofs.WG.Queues.PollRouting
import Leanux.Proofs.WG.Queues.RxPollReceiptLink

/-! A supplied routing state reaches the actual Stack entry through the existing
once-only poll journal. Receipt ordering and routing are proved independently
and joined on the identical emitted suffix, including a later Stop. -/
namespace Leanux.Proofs.WG.Queues.PollAuthorization
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.AllowedIps
open Lifetimes RxJoint

/-- Both certificates describe exactly the same fresh global suffix. Incoming
histories remain arbitrary and do not provide any of the new receipt witnesses. -/
theorem observePoll_joined (xs : FlatTable × FlatTable) (pid : PeerId) (budget : Nat)
    (w : World) (h : List RxHistory.Event) (hi : RoutedView (routingView w.wg) xs) :
    ∃ suffix : List Event,
      (runPrefix (RxHistory.observePoll pid budget) w h).2 = h ++ suffix.map RxHistory.promote ∧
      PollRouting.Safe xs suffix ∧ RxLink.Linked [] suffix := by
  obtain ⟨s,_,run,linked⟩ := RxLink.observePoll_link_suffix pid budget w h
  obtain ⟨t,hist,safe,_⟩ := PollRouting.observePoll xs pid budget w h hi
  have same : s.map RxHistory.promote = t.map RxHistory.promote :=
    List.append_cancel_left ((congrArg Prod.snd run).symm.trans hist)
  have decoded := congrArg (List.filterMap RxLink.historyEvent) same
  simp only [RxLink.promote_history] at decoded
  subst t
  exact ⟨s,congrArg Prod.snd run,safe,linked⟩

/-- Every actual Stack entry has a strictly earlier successful consume in this
same suffix. Its bytes use the peer selected by the poll's flat source table.
This is routing authorization of a raw peer slot, not historical key identity. -/
theorem entered_routed (xs : FlatTable × FlatTable) (suffix : List Event)
    (safe : PollRouting.Safe xs suffix) (linked : RxLink.Linked [] suffix)
    (e : RxJoint.Entry) (entered : Event.entered e ∈ suffix) :
    ∃ (r : RxDisposition.ConsumeReceipt), ∃ before between after,
      suffix = before ++ [.consumed e.tag.occurrence e.tag.skb e.stamp r] ++
        between ++ [.entered e] ++ after ∧
      e.origin = some r ∧ r.run.value = some e.tag.bytes ∧
      RxLink.Source e.tag.skb e.stamp r ∧
      RoutedView (routingView r.run.before) xs ∧
      ∃ v4 : Bool,
        ipTunnelParseProtocol e.tag.bytes = (if v4 then 4 else 6) ∧
        ipTunnelParseProtocol r.packet.bytes = (if v4 then 4 else 6) ∧
        PeerWinner (rootWidth v4) (sourceAddress v4 e.tag.bytes)
          (selectedFlat v4 xs) (some r.peer) ∧
        sourceAddress v4 e.tag.bytes = sourceAddress v4 r.packet.bytes := by
  obtain ⟨s,hs,events⟩ := linked.events
  simp only [List.nil_append] at hs
  subst s
  obtain ⟨pre,after,split,buffered⟩ := events (.entered e) entered
  change RxLink.Buffered [] ([] ++ pre) e at buffered
  simp only [List.nil_append] at buffered
  obtain ⟨beforeBuffer,afterBuffer,hbuffer,consumed⟩ := buffered
  obtain ⟨r,before,afterConsume,origin,value,source,hconsume,_⟩ := consumed
  simp only [List.nil_append] at hbuffer hconsume
  have combined : suffix = before ++ [.consumed e.tag.occurrence e.tag.skb e.stamp r] ++
      (afterConsume ++ [.buffered e] ++ afterBuffer) ++ [.entered e] ++ after := by
    simp only [split,hbuffer,hconsume,List.append_assoc]
  have member : Event.consumed e.tag.occurrence e.tag.skb e.stamp r ∈ suffix := by
    rw [combined]
    simp
  have routed := (safe r (List.mem_filterMap.mpr ⟨_,member,rfl⟩)).1
  refine ⟨r,before,afterConsume ++ [.buffered e] ++ afterBuffer,after,combined,
    origin,value,source,routed,?_⟩
  apply Packets.consumeDataDone_authorized r.peer r.packet r.endpoint r.run.before r.run.after
    r.run.ambientBefore r.run.ambientAfter e.tag.bytes xs routed
  simpa only [RxDisposition.ConsumeReceipt.Valid,WGRunWitness.Valid,value] using source.1

/-- Concrete poll observation, with exact promotion and an ordered routing
witness for each entry it actually emits. No normal-return premise is needed. -/
theorem observePoll_entries (xs : FlatTable × FlatTable) (pid : PeerId) (budget : Nat)
    (w : World) (h : List RxHistory.Event) (hi : RoutedView (routingView w.wg) xs) :
    ∃ suffix : List Event,
      (runPrefix (RxHistory.observePoll pid budget) w h).2 = h ++ suffix.map RxHistory.promote ∧
      ∀ e, Event.entered e ∈ suffix →
        ∃ (r : RxDisposition.ConsumeReceipt), ∃ before between after,
          suffix = before ++ [.consumed e.tag.occurrence e.tag.skb e.stamp r] ++
            between ++ [.entered e] ++ after ∧
          e.origin = some r ∧ r.run.value = some e.tag.bytes ∧
          RxLink.Source e.tag.skb e.stamp r ∧
          RoutedView (routingView r.run.before) xs ∧
          ∃ v4 : Bool,
            ipTunnelParseProtocol e.tag.bytes = (if v4 then 4 else 6) ∧
            ipTunnelParseProtocol r.packet.bytes = (if v4 then 4 else 6) ∧
            PeerWinner (rootWidth v4) (sourceAddress v4 e.tag.bytes)
              (selectedFlat v4 xs) (some r.peer) ∧
            sourceAddress v4 e.tag.bytes = sourceAddress v4 r.packet.bytes := by
  obtain ⟨suffix,hist,safe,linked⟩ := observePoll_joined xs pid budget w h hi
  exact ⟨suffix,hist,entered_routed xs suffix safe linked⟩

end Leanux.Proofs.WG.Queues.PollAuthorization
