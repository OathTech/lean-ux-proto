import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionCallbackFrames

/-! Fixed encryption callback points are selected by their actual head read,
ordered loop and publication prefix. Source witnesses contain no accounting
premise. Nested release keeps its own native pending-receipt evidence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCallback
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open CompleteCarrier EncryptionPacket EncryptionInterior

inductive Point : Option (List SkbId) → World → List Event → World → List Event → Prop where
  | entry : Point item w h w h
  | returned (performed : runPrefix (CausalJournal.encrypt item) w h=(.ok (value,v),last)) : Point item w h v last
  | pendingReturn (performed : runPrefix (HandshakeSecurity.StagedDisposal.EncryptionSource.tail ops item)
      w h=(.ok (value,v),last)) : Point item w h v last
  | head (captured : runPrefix (headPrefix items) w h=(.ok ((headId,head),u),middle)) : Point (some items) w h u middle
  | loop {packetState : PacketState} (captured : runPrefix (headPrefix items) w h=(.ok ((headId,head),u),middle))
      (ordered : items=done++rest)
      (walk : Walk headId head done .crypted u middle packetState v last) : Point (some items) w h v last
  | read {packetState : PacketState} {read : RunWitness DataPacket} (captured : runPrefix (headPrefix items) w h=(.ok ((headId,head),u),middle))
      (ordered : items=done++skb::rest)
      (walk : Walk headId head done .crypted u middle packetState v last)
      (performed : runPrefix (readPrefix skb) v last=(.ok (read,q),events)) : Point (some items) w h q events
  | write {packetState : PacketState} {read : RunWitness DataPacket} (captured : runPrefix (headPrefix items) w h=(.ok ((headId,head),u),middle))
      (ordered : items=done++skb::rest)
      (walk : Walk headId head done .crypted u middle packetState v last)
      (performed : runPrefix (writePrefix headId head skb) v last=(.ok ((read,encrypted),q),events)) :
      Point (some items) w h q events
  | bytes {packetState : PacketState} {read : RunWitness DataPacket} (captured : runPrefix (headPrefix items) w h=(.ok ((headId,head),u),middle))
      (ordered : items=done++skb::rest)
      (walk : Walk headId head done .crypted u middle packetState v last)
      (prepared : runPrefix (writePrefix headId head skb) v last=(.ok ((read,some bytes),q),events))
      (written : runPrefix (ops.step (liftWG (setTxSkb skb fun p=>{p with bytes}))) q events=(.ok ((),t),after)) :
      Point (some items) w h t after
  | publication {packetState : PacketState} (entered : runPrefix (callbackPublicationPrefix items) w h=
      (.ok ((headId,head,packetState),u),middle)) : Point (some items) w h u middle
  | published {packetState : PacketState} (entered : runPrefix (callbackPublicationPrefix items) w h=
        (.ok ((headId,head,packetState),u),middle))
      (performed : runPrefix (publicationPrefixAt site items packetState) u middle=
        (.ok ((first,pid),v),last)) : Point (some items) w h v last
  | release {packetState : PacketState} (entered : runPrefix (callbackPublicationPrefix items) w h=
        (.ok ((headId,head,packetState),u),middle))
      (performed : runPrefix (publicationPrefixAt .scheduled items packetState) u middle=
        (.ok ((first,pid),v),last))
      (point : PeerRetirement.Points.NativePoints (some pid) v last q events) : Point (some items) w h q events

inductive Evidence (ledger : Staged.Obligations.Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) : List Event → World → Prop where
  | accounted (account : Accounted h ledger debts locals w.wg) : Evidence ledger debts locals h w
  | release (evidence : PeerRetirement.Points.Evidence ledger debts locals h w.wg) : Evidence ledger debts locals h w

/-- Every declared encryption callback point preserves the original packet
ledger or carries the actual pending release receipt; no packet account is
assumed at an interior point or inferred from a later completed callback. -/
theorem Point.evidence (point : Point item w h v last)
    (before : Accounted h ledger debts locals w.wg) : Evidence ledger debts locals last v := by
  cases point with
  | entry=>exact .accounted before
  | returned performed=>exact .accounted (normal_accounted before performed)
  | pendingReturn performed=>exact .accounted (tail_accounted before performed)
  | head captured=>exact .accounted (head_prefix_current before captured).2.2.2.2.1
  | loop captured _ walk=>exact .accounted (walk.accounted (head_prefix_current before captured).2.2.2.2.1)
  | read captured _ walk performed=>
    have atPacket:=walk.accounted (head_prefix_current before captured).2.2.2.2.1
    exact .accounted (read_current atPacket performed).2.2.2.2.2
  | write captured _ walk performed=>
    exact .accounted (write_accounted (walk.accounted (head_prefix_current before captured).2.2.2.2.1) performed)
  | bytes captured _ walk prepared written=>
    have atWrite:=write_accounted (walk.accounted (head_prefix_current before captured).2.2.2.2.1) prepared
    exact .accounted (bytes_accounted atWrite written)
  | publication entered=>exact .accounted (publication_accounted before entered)
  | published entered performed=>
    exact .accounted (publication_prefix_accounted _ (publication_accounted before entered) performed)
  | release entered performed point=>
    exact .release (PeerRetirement.Points.native_evidence
      (publication_prefix_accounted _ (publication_accounted before entered) performed) point)

theorem Point.residual (point : Point item w h v last) :
    ∃remaining,runPrefix (CausalJournal.encrypt item) w h=runPrefix remaining v last := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | returned performed=>exact ⟨pure _,performed⟩
  | pendingReturn performed=>exact ⟨_,pending_return_residual performed⟩
  | head captured=>exact ⟨_,head_residual captured⟩
  | loop captured ordered walk=>exact ⟨_,loop_residual captured ordered walk⟩
  | read captured ordered walk performed=>exact ⟨_,read_residual captured ordered walk performed⟩
  | write captured ordered walk performed=>exact ⟨_,write_residual captured ordered walk performed⟩
  | bytes captured ordered walk prepared written=>exact ⟨_,byte_residual captured ordered walk prepared written⟩
  | publication entered=>exact ⟨_,publication_residual entered⟩
  | published entered performed=>exact ⟨_,publication_site_residual entered performed⟩
  | release entered performed point=>exact ⟨_,release_residual entered performed point⟩

noncomputable def remainder (item : Option (List SkbId)) (w : World) (h : List Event)
    (v : World) (last : List Event) (point : Point item w h v last) : PrefixM Event Bool :=
  Classical.choose point.residual

theorem remainder_run (point : Point item w h v last) :
    runPrefix (CausalJournal.encrypt item) w h=runPrefix (remainder item w h v last point) v last :=
  Classical.choose_spec point.residual

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCallback
