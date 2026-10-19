import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDriverCuts
import Leanux.Proofs.WG.RetirementSecurity.HolderPoll
import Leanux.Proofs.WG.TransmitSecurity.EncryptReceipts

/-! A ready TX batch must have completed every member's byte write. Empty
fresh buffers are permitted until the head is published CRYPTED. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
variable {id : SkbId}

def Nonempty (id : SkbId) (w : WGWorld) : Prop :=
  ∀p,TxDisposition.txPackets w id=some p→p.bytes≠[]

def Complete (items : List SkbId) (w : WGWorld) : Prop :=
  ∀id∈items,Nonempty id w

def Inv (w : WGWorld) : Prop :=
  ∀pid p,peerAt w pid=some p→∀items∈p.txQueue.all,∀first,
    items.head?=some first→TxDisposition.HeadState first .crypted w→Complete items w

theorem initial (net bare : Bool) : Inv (Runner.initialWG net bare) := by
  cases net <;> cases bare <;> simp [Inv,peerAt,Runner.initialWG]

theorem Nonempty.frame (before : Nonempty id w)
    (same : TxDisposition.txPackets v id=TxDisposition.txPackets w id) : Nonempty id v :=
  fun p resident=>before p (same ▸ resident)

theorem encryption_nonempty (checksum : Packet→Leanux.M Packet) (key : KeypairId) (packet : DataPacket)
    (run : (encryptPacket checksum key packet).run w=.ok (some bytes,v)) : bytes≠[] := by
  obtain ⟨r,_,_,_,_,_,same⟩ := TransmitSecurity.Encryption.original_success_receipt checksum key packet w v bytes [] run
  rw [←same]
  simp [TransmitSecurity.Encryption.Receipt.ciphertext,dataMessage,le32,List.range_succ]

theorem write (id : SkbId) (bytes : List UInt8) (nonempty : bytes≠[]) (target : SkbId) :
    Hoare (setTxSkb id (fun p=>{p with bytes}))
      (fun w=>id=target ∨ Nonempty target w) (fun _=>Nonempty target) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  cases device:w.dev with
  | none=>simp [setTxSkb,liftSkb_run,device] at run
  | some d=>
    cases stored:d.txSkbs[id]? with
    | none=>
      simp [setTxSkb,liftSkb_run,SkbStore.setTx,SkbStore.getTx,device,stored,invariant,AmbientM.invariant] at run
      cases run
    | some p=>
      rw [Packets.setTxSkb_run w a d id p (fun p=>{p with bytes}) device stored] at run
      cases run
      intro q resident
      by_cases same:id=target
      · subst target
        have value:{p with bytes}=q:=by simpa [TxDisposition.txPackets,Packets.update,device] using resident
        subst q
        exact nonempty
      · exact (before.resolve_left same) q
          (by simpa [TxDisposition.txPackets,Packets.update,device,Std.TreeMap.getElem?_insert,same] using resident)

theorem write_keeps (id : SkbId) (bytes : List UInt8) (nonempty : bytes≠[]) (target : SkbId) :
    Preserves (Nonempty target) (setTxSkb id (fun p=>{p with bytes})) :=
  hoare_consequence (write id bytes nonempty target) (fun _ before=>.inr before) (fun _ _ before=>before)

def body (key : KeypairId) (id : SkbId) (state : PacketState) : Leanux.M (ForInStep PacketState) := do
  _←branch .encWorkerSkbIterate true
  let encrypted←encryptPacket Env.checksumHelp key (←getTxSkb id)
  if ←branch .encWorkerEncrypted encrypted.isSome then
    setTxSkb id fun p=>{p with bytes:=encrypted.getD []}
    return .yield state
  else return .done .dead

theorem body_result (key : KeypairId) (id target : SkbId) (state : PacketState) :
    Hoare (body key id state) (fun w=>id=target ∨ Nonempty target w.wg)
      (fun out w=>out=.done .dead ∨ out=.yield state ∧ Nonempty target w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w out v before run
  unfold body at run
  simp only [MaterialOrigin.bind_ok] at run
  obtain ⟨_,u,iterate,packet,t,read,encrypted,s,crypt,yes,z,check,tail⟩ := run
  cases iterate
  have readNative := HolderPoll.native_receipt read
  obtain ⟨same,_,_,_,_⟩ := Packets.getTxSkb_current id w.wg t.wg packet _ t.ambient readNative
  have kept := (ProjectedAction.iff_run _ _ _).mp (encrypt_packet_store key packet) t encrypted s crypt
  have sameCell : TxDisposition.txPackets s.wg target=TxDisposition.txPackets w.wg target := by
    have dev:s.wg.dev=t.wg.dev:=congrArg WGStoreView.dev kept
    simp only [TxDisposition.txPackets,dev,same]
  cases check
  cases encrypted with
  | none=>
    simp only [Option.isSome_none,Bool.false_eq_true,ite_false] at tail
    cases tail
    exact .inl rfl
  | some bytes=>
    simp only [Option.isSome_some,ite_true,MaterialOrigin.bind_ok] at tail
    obtain ⟨value,last,writeRun,returned⟩ := tail
    cases value
    cases returned
    have input:id=target ∨ Nonempty target s.wg:=before.imp_right (fun old=>old.frame sameCell)
    have paid:=HolderPoll.native_receipt writeRun
    exact .inr ⟨rfl,(hoare_iff_run_ambient _ _ _).mp (write id bytes (encryption_nonempty _ _ _ crypt) target)
      s.wg _ () v.wg _ input paid⟩

theorem body_run (key : KeypairId) (id : SkbId) (state : PacketState)
    (run : (body key id state).run w=.ok (out,v)) :
    out=.done .dead ∨ out=.yield state ∧ Nonempty id v.wg ∧
      ∀target,Nonempty target w.wg→Nonempty target v.wg := by
  rcases (hoare_iff_run _ _ _).mp (body_result key id id state) w out v (.inl rfl) run with dead | ⟨yes,nonempty⟩
  · exact .inl dead
  · refine .inr ⟨yes,nonempty,?_⟩
    intro target before
    rcases (hoare_iff_run _ _ _).mp (body_result key id target state) w out v (.inr before) run with dead | kept
    · rw [yes] at dead; cases dead
    · exact kept.2

theorem loop_target (items : List SkbId) (key : KeypairId) (target : SkbId)
    (state : PacketState) (w v : World) (result : PacketState)
    (before : target∉items→Nonempty target w.wg)
    (run : (forIn items state (body key)).run w=.ok (result,v))
    (complete : result=.crypted) : Nonempty target v.wg := by
  induction items generalizing state w with
  | nil=>
    simp only [List.forIn_nil] at run
    cases run
    exact before (by simp)
  | cons id rest ih=>
    rw [List.forIn_cons,MaterialOrigin.bind_ok] at run
    obtain ⟨step,u,head,tail⟩ := run
    rcases body_run key id state head with dead | ⟨yes,nonempty,kept⟩
    · rw [dead] at tail
      cases tail
      cases complete
    · rw [yes] at tail
      apply ih state u (fun absent=>?_) tail
      by_cases same:target=id
      · subst target; exact nonempty
      · exact kept target (before (by simp [same,absent]))

theorem loop_complete (items : List SkbId) (key : KeypairId) (state : PacketState)
    (run : (forIn items state (body key)).run w=.ok (.crypted,v)) : Complete items v.wg := by
  intro target member
  exact loop_target items key target state w v .crypted (fun absent=>(absent member).elim) run rfl

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
