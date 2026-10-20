import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionCallbackSource

/-! Same-ledger frames for the fixed encryption callback prefixes. History
transport is justified separately from native byte/state mutation, and only
actual successful source prefixes produce an account at a returned world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCallback
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity CausalJournal
open CompleteCarrier EncryptionPacket EncryptionInterior Staged.Obligations
set_option maxHeartbeats 600000
variable {packetState : PacketState} {read : RunWitness DataPacket}

theorem normal_accounted (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix (CausalJournal.encrypt item) w h=(.ok (value,v),last)) :
    Accounted last ledger debts locals v.wg := by
  obtain ⟨suffix,grown,birthFree⟩:=CompleteEncrypt.birth_suffix item w h
  rw [performed] at grown
  change last=h++suffix at grown
  have native:=(CompleteEncrypt.erases item w h).symm.trans (congrArg Prod.fst performed)
  have kept:=(hoare_iff_run _ _ _).mp (Encrypt.tail item) w value v before.entry native
  obtain ⟨_,_,complete,_⟩:=CompleteEncrypt.history item w h before.complete
  rw [performed] at complete
  refine ⟨?_,complete⟩
  rw [grown]
  exact Queued.Inv.history kept suffix birthFree

theorem write_accounted (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix (writePrefix headId head skb) w h=(.ok ((read,encrypted),v),last)) :
    Accounted last ledger debts locals v.wg := by
  rw [writePrefix,runPrefix_bind] at performed
  cases readRun : runPrefix (readPrefix skb) w h with
  | mk result middle=>
    rw [readRun] at performed
    cases result with
    | error stop=>cases performed
    | ok pair=>
      obtain ⟨actual,u⟩:=pair
      have atRead:=(read_current before readRun).2.2.2.2.2
      dsimp only at performed
      rw [runPrefix_bind] at performed
      cases cryptRun : runPrefix (crypt headId head skb actual) u middle with
      | mk result after=>
        rw [cryptRun] at performed
        cases result with
        | error stop=>cases performed
        | ok pair=>
          obtain ⟨bytes,q⟩:=pair
          have atCrypt:=crypt_accounted atRead cryptRun
          dsimp only at performed
          rw [runPrefix_bind,branch_run] at performed
          cases performed
          exact atCrypt

theorem publication_prepared (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix (publicationPrefix headId head items) w h=(.ok (packetState,v),last)) :
    Accounted last ledger debts locals v.wg := by
  rw [publicationPrefix,runPrefix_bind] at performed
  cases walked : runPrefix (loop headId head items .crypted) w h with
  | mk result middle=>
    rw [walked] at performed
    cases result with
    | error stop=>cases performed
    | ok pair=>
      obtain ⟨next,u⟩:=pair
      have atLoop:=loop_accounted before walked
      obtain ⟨q,guarded,same⟩:=guard_total next u middle
      dsimp only at performed
      rw [runPrefix_bind,guarded] at performed
      cases performed
      rw [same]
      exact atLoop

theorem publication_accounted (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix (callbackPublicationPrefix items) w h=(.ok ((headId,head,packetState),v),last)) :
    Accounted last ledger debts locals v.wg := by
  rw [callbackPublicationPrefix,runPrefix_bind] at performed
  cases captured : runPrefix (headPrefix items) w h with
  | mk result middle=>
    rw [captured] at performed
    cases result with
    | error stop=>cases performed
    | ok pair=>
      obtain ⟨⟨first,receipt⟩,u⟩:=pair
      have atHead:=(head_prefix_current before captured).2.2.2.2.1
      dsimp only at performed
      rw [runPrefix_bind] at performed
      cases prepared : runPrefix (publicationPrefix first receipt items) u middle with
      | mk result after=>
        rw [prepared] at performed
        cases result with
        | error stop=>cases performed
        | ok pair=>
          obtain ⟨next,q⟩:=pair
          cases performed
          exact publication_prepared atHead prepared

theorem publication_return_accounted (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix (ops.publish items packetState) w h=(.ok ((),v),last)) :
    Accounted last ledger debts locals v.wg := by
  classical
  let body := HandshakeSecurity.StagedDisposal.Publication.observed
    Event.stagedDisposal stagedDisposal? items packetState
  let ρ : Event → Option Unit := fun event=>if birthPackets event=[] then none else some ()
  have quiet : HistoryFrame ρ (liftWGObserver body) :=
    (HandshakeSecurity.StagedDisposal.Publication.frame
      (HandshakeSecurity.StagedDisposal.Decoration.release Event.stagedDisposal stagedDisposal?)
      (fun peer wg=>focusPrefix_other _ _ ρ (fun _=>by simp [ρ,birthPackets])
        ((HandshakeSecurity.StagedDisposal.releaseObserved peer).run wg)) items packetState).liftWGObserver
  obtain ⟨suffix,grown⟩ := (HandshakeSecurity.StagedDisposal.Publication.appends
    (HandshakeSecurity.StagedDisposal.Decoration.release Event.stagedDisposal stagedDisposal?)
    (fun _=>StateAppends.focus _ _ _) items packetState).liftWGObserver w h
  have native := (liftWGObserver_erases
    (HandshakeSecurity.StagedDisposal.Publication.observed_erases
      Event.stagedDisposal stagedDisposal? items packetState) w h).symm.trans (congrArg Prod.fst performed)
  have kept := (hoare_iff_run _ _ _).mp
    (PublicationPoll.native_product _ _ (Encrypt.publication items packetState))
    w () v before.entry native
  have complete := CompleteEncrypt.publication_complete items packetState w.wg w.ambient before.complete
  have filtered := quiet w h
  change (runPrefix (ops.publish items packetState) w h).2=h++suffix at grown
  change (runPrefix (ops.publish items packetState) w h).2.filterMap ρ=h.filterMap ρ at filtered
  change StagedTerminalComplete.Complete (runPrefix (ops.publish items packetState) w h).2 ledger at complete
  rw [performed] at grown filtered complete
  change last=h++suffix at grown
  change last.filterMap ρ=h.filterMap ρ at filtered
  rw [grown,List.filterMap_append] at filtered
  have empty : suffix.filterMap ρ=[] := List.append_right_eq_self.mp filtered
  refine ⟨?_,complete⟩
  rw [grown]
  apply Queued.Inv.history kept suffix
  intro event member
  by_cases noBirth : birthPackets event=[]
  · exact noBirth
  have bad : () ∈ suffix.filterMap ρ := List.mem_filterMap.mpr ⟨event,member,by simp [ρ,noBirth]⟩
  rw [empty] at bad
  cases bad

theorem tail_accounted (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix (HandshakeSecurity.StagedDisposal.EncryptionSource.tail ops item) w h=
      (.ok (value,v),last)) : Accounted last ledger debts locals v.wg := by
  cases item with
  | none=>
    simp only [HandshakeSecurity.StagedDisposal.EncryptionSource.tail,Option.isSome_none,
      runPrefix_bind,branch_run] at performed
    cases performed
    exact before
  | some items=>
    rw [publication_source,runPrefix_bind] at performed
    cases prepared : runPrefix (callbackPublicationPrefix items) w h with
    | mk result middle=>
      rw [prepared] at performed
      cases result with
      | error stop=>cases performed
      | ok pair=>
        obtain ⟨⟨first,head,state⟩,u⟩:=pair
        have atPublication:=publication_accounted before prepared
        dsimp only at performed
        rw [publish,runPrefix_bind] at performed
        cases published : runPrefix (ops.publish items state) u middle with
        | mk result after=>
          rw [published] at performed
          cases result with
          | error stop=>cases performed
          | ok pair=>
            obtain ⟨ignored,q⟩:=pair
            cases ignored
            cases performed
            exact publication_return_accounted atPublication published

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCallback
