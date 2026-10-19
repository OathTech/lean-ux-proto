import Leanux.Proofs.WG.RetirementSecurity.HolderNapiKeys
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDecrypt
import Leanux.Proofs.WG.Queues.BaseCoherenceWorkers

/-! Native decrypt preparation retains every key credit. Successful plaintext
replacement keeps the key word of the actual saved RX cell; publication's
extra peer reference is not charged to the independent key ledger. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDecryptKeys
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open CurrentPoll CurrentTraffic
variable {id : SkbId}

theorem publish_points (skb : SkbId) (state : PacketState) :
    SameView ownershipPointView (RxWorkers.publishSource skb state) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a pid v b run
  obtain ⟨d,pkt,k,p,device,packet,_,_,peer,effect⟩ :=
    PublicationIdentity.publish_execution skb state w v a b pid run
  have after := congrArg WGStoreView.dev effect
  change v.dev=some _ at after
  unfold ownershipPointView keyReferenceView ownershipAt peerAt keyAt packetKeyWords
  simp only [after,device,Option.bind_some,Option.isSome_some,Prod.mk.injEq]
  refine ⟨True.intro,True.intro,?_,True.intro,?_⟩
  · funext other
    by_cases same:pid=other
    · subst other
      simp [peer,peerOwnership,slotFields]
    · simp [Std.TreeMap.getElem?_insert,same]
  · funext other
    by_cases same:skb=other
    · subst other
      simp [packet]
    · simp [Std.TreeMap.getElem?_insert,same]

theorem payload_keys (keys : HolderAccount temporary w) (device : w.dev=some d)
    (stored : d.rxSkbs[id]?=some pkt) (key : out.keypair=pkt.keypair) (a b : Ambient)
    (run : ((setRxSkb id (fun _=>out)).run w).run a=.ok (((),v),b)) : HolderAccount temporary v := by
  rw [Packets.setRxSkb_run w a d id pkt (fun _=>out) device stored] at run
  cases run
  apply keys.store
  unfold holderStore Origins.view peersAt packetKeyWords
  simp only [Packets.update,device,Option.map_some,Option.bind_some,Prod.mk.injEq]
  refine ⟨True.intro,True.intro,True.intro,?_⟩
  funext other
  by_cases same:id=other
  · subst other
    simp [stored,key]
  · simp [Std.TreeMap.getElem?_insert,same]

theorem read_decrypt (keys : HolderAccount temporary w) (a b : Ambient)
    (run : ((RxOrigin.readDecrypt id).run w).run a=.ok (((pkt,result),v),b)) :
    HolderAccount temporary v ∧ (∃d,v.dev=some d ∧ d.rxSkbs[id]?=some pkt) ∧
      ∀out,result=some out → out.keypair=pkt.keypair := by
  unfold RxOrigin.readDecrypt at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨old,u,c,read,answer,t,e,decrypt,finish⟩ := run
  cases finish
  obtain ⟨world,ambient,d,device,stored⟩ := Packets.getRxSkb_current id w u pkt a c read
  subst u
  subst c
  have after := (hoare_iff_run_ambient _ _ _).mp (HolderReplay.decrypt pkt) w a result v b keys decrypt
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDecrypt.«0».Leanux.Proofs.WG.OwnerDecrypt.decryptPacket_rx) pkt)
    w a result v b decrypt
  have cell : (v.dev.bind fun d=>d.rxSkbs[id]?)=some pkt := by
    have found := congrFun (congrArg Prod.snd same) id
    simpa [RxDisposition.nativeRxStore,RxCredits.rxView,device,stored] using found
  refine ⟨after,Option.bind_eq_some_iff.mp cell,?_⟩
  intro out present
  obtain ⟨_,_,_,_,_,key,_⟩ := Affiliation.decryptPacket_fields pkt out w v a b (present ▸ decrypt)
  exact key

theorem prepare_keys : Preserves (HolderAccount temporary) RxWorkers.prepareSource := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b keys run
  rw [DecryptCarrier.prepare_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,u,c,read,tail⟩ := run
  obtain ⟨world,ambient,device⟩ := DecryptCarrier.getDev_current a c read
  subst u
  subst c
  cases consumed:d.decryptQueue.consume with
  | mk item ring=>cases item with
    | none=>
      simp only [consumed,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨answer,u,c,branch,finish⟩ := tail
      cases branch
      cases finish
      exact keys
    | some skb=>
      simp only [consumed,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨answer,u,c,branch,_,ringWorld,e,install,pair,readWorld,f,decrypt,decision,decWorld,g,chosen,tail⟩ := tail
      cases branch
      have installed := keys.points ((ProjectedAction.iff_run_ambient _ _ _).mp
        (ownership_modifyDev (fun d=>{d with decryptQueue:=ring})
          (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)) w _ () ringWorld e install)
      obtain ⟨pkt,decrypted⟩ := pair
      obtain ⟨held,⟨dev,found,packet⟩,fields⟩ := read_decrypt installed e f decrypt
      cases chosen
      cases decrypted with
      | none=>
        simp only [Option.isSome_none,Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨pid,final,clock,publish,finish⟩ := tail
        cases finish
        exact held.points ((ProjectedAction.iff_run_ambient _ _ _).mp (publish_points skb .dead)
          readWorld _ pid v b publish)
      | some out=>
        simp only [Option.isSome_some,ite_true,MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨_,updated,clock,write,pid,final,last,publish,finish⟩ := tail
        cases finish
        have written := payload_keys held found packet (fields out rfl) _ clock write
        exact written.points ((ProjectedAction.iff_run_ambient _ _ _).mp (publish_points skb .crypted)
          updated clock pid v b publish)

theorem prepare_current : Preserves (CurrentLifecycle.Inv sessions) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config:={zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head decryptPacket; exact CurrentRx.decryptPacket_preserves _ sessions)
    | (rx_retention_head RxWorkers.publishSource; exact CurrentWorkers.publish_preserves _ _ sessions)
    | (rx_retention_head setRxSkb; unfold setRxSkb)
    | current_poll_native sessions

theorem prepare_support : Preserves (HolderPoll.Support sessions locals active) RxWorkers.prepareSource :=
  HolderPoll.join OccurrenceDecrypt.prepare prepare_current BaseCoherence.prepareSource_view
    (KeySlotLiveness.decrypt_prepare (pending:=[]))

end Leanux.Proofs.WG.RetirementSecurity.HolderDecryptKeys
