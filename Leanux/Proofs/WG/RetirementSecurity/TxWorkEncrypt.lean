import Leanux.Proofs.WG.RetirementSecurity.TxWorkByteFrames

/-! The actual selected encrypt continuation preserves service through each
byte write and consumes it only at terminal DEAD/CRYPTED publication. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

abbrev EncryptKept (locals : List TxLocalBatch) (crypt : List (List SkbId))
    (tx : List PeerId) (w : WGWorld) := Obligations crypt tx w ∧ TxInventory locals w

theorem encrypt_body (key id : Nat) (state : PacketState) :
    Preserves (fun w : World=>EncryptKept locals crypt tx w.wg) (ReadyCiphertext.body key id state) := by
  let Q := EncryptKept locals crypt tx
  let P := fun w : World=>Q w.wg
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : Leanux.M α) :=
    productAmbient_spec action P (fun _ _ before=>before)
  have readNative (id : SkbId) : Preserves Q (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a packet v b before run
    exact (Packets.getTxSkb_current id w v packet a b run).1 ▸ before
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product Q _ (readNative id)
  have writeNative (id : SkbId) (bytes : List UInt8) :
      Preserves Q (setTxSkb id (fun p=>{p with bytes})) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact ⟨before.1.write_bytes id bytes a b run,before.2.points
      ((ProjectedAction.iff_run_ambient _ _ _).mp
        (ownershipPoints_holderStore _ (setTx_holderStore id (fun p=>{p with bytes}) (fun _=>rfl)))
          w a () v b run)⟩
  have write (id : SkbId) (bytes : List UInt8) :
      Preserves P (monadLift (setTxSkb id (fun p=>{p with bytes})) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (writeNative id bytes)
  have encrypt (key : KeypairId) (packet : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key packet) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    exact ⟨before.1.store ((ProjectedAction.iff_run _ _ _).mp (encrypt_packet_store key packet)
      w result v run),before.2.encrypt_packet key packet run⟩
  change Preserves P _
  routing_tx_source [ReadyCiphertext.body] using [read,write,encrypt,ambient]

theorem encrypt_loop (items : List SkbId) (key : KeypairId) (state : PacketState) :
    Preserves (fun w : World=>EncryptKept locals crypt tx w.wg)
      (forIn items state (ReadyCiphertext.body key)) := by
  apply list_view_spec id (fun w : World=>EncryptKept locals crypt tx w.wg)
  intro id mark
  exact encrypt_body key id mark

theorem encrypt_loop_terminal (items : List SkbId) (key : KeypairId) (state : PacketState)
    (terminal : state≠.uncrypted)
    (run : (forIn items state (ReadyCiphertext.body key)).run w=.ok (result,v)) :
    result≠.uncrypted := by
  induction items generalizing state w with
  | nil=>simp only [List.forIn_nil] at run; cases run; exact terminal
  | cons id rest ih=>
    rw [List.forIn_cons,MaterialOrigin.bind_ok] at run
    obtain ⟨step,u,body,tail⟩:=run
    rcases ReadyCiphertext.body_run key id state body with dead | ⟨yes,_,_⟩
    · rw [dead] at tail
      cases tail
      decide
    · rw [yes] at tail
      exact ih state terminal tail

theorem Obligations.encrypt_tail (before : Obligations (item.toList++crypt) tx w.wg)
    (inventory : TxInventory locals w.wg)
    (run : (RxWorkers.encryptStepTailSource item).run w=.ok (result,v)) :
    Obligations crypt tx v.wg := by
  cases item with
  | none=>cases run; exact before
  | some items=>
    cases head:items.head? with
    | none=>
      simp only [RxWorkers.encryptStepTailSource,head,MaterialOrigin.bind_ok] at run
      obtain ⟨_,u,_,stopped⟩:=run
      cases stopped
    | some first=>
      rw [ReadyCiphertext.source items first head] at run
      simp only [MaterialOrigin.bind_ok] at run
      obtain ⟨_,u,consumed,saved,t,read,state,s,loop,tail⟩:=run
      have consumedWorld:u.wg=w.wg := by cases consumed; rfl
      have readWorld:t.wg=u.wg := (Packets.getTxSkb_current first u.wg t.wg saved u.ambient t.ambient
        (HolderPoll.native_receipt read)).1
      have input:EncryptKept locals (items::crypt) tx t.wg := by
        simpa only [readWorld,consumedWorld,Option.toList_some,List.singleton_append] using And.intro before inventory
      have kept:=(hoare_iff_run _ _ _).mp (encrypt_loop items saved.keypair .crypted)
        t state s input loop
      have terminal:=encrypt_loop_terminal items saved.keypair .crypted (by decide) loop
      have finish (z : World) (same:z.wg=s.wg)
          (run : (do enqueuePerPeerTx items state; pure true : Leanux.M Bool).run z=.ok (result,v)) :
          Obligations crypt tx v.wg := by
        rw [MaterialOrigin.bind_ok] at run
        obtain ⟨_,last,published,returned⟩:=run
        cases returned
        exact (same ▸ kept.1).publish (same ▸ kept.2) state terminal z.ambient v.ambient
          (HolderPoll.native_receipt published)
      split at tail
      · rw [MaterialOrigin.bind_ok] at tail
        obtain ⟨_,z,step,tail⟩:=tail
        have same:z.wg=s.wg := by cases step; rfl
        exact finish z same tail
      · exact finish s rfl tail

end Leanux.Proofs.WG.RetirementSecurity.TxWork
