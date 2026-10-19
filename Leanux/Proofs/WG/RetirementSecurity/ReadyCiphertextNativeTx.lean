import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeEncrypt

/-! Native TX completion retains ready ciphertext; cached selection,
queue removal and final disposal can only remove ready occurrences. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Tx
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits Native

theorem replace_subset (before : Inv w) (device : w.dev = some d)
    (found : d.peers[pid]? = some p) (subset : q.txQueue.all ⊆ p.txQueue.all) :
    Inv (replacePeer w d pid q) := by
  apply before.transport
  · intro other r resident items member
    by_cases same : pid = other
    · subst other
      have equal : r = q := by simpa [peerAt,replacePeer] using resident.symm
      subst r
      exact ⟨p,by simp [peerAt,device,found],subset member⟩
    · exact ⟨r,by simpa [peerAt,replacePeer,device,Std.TreeMap.getElem?_insert,same] using resident,member⟩
  · intro id packet resident
    exact ⟨packet,by simpa [TxDisposition.txPackets,replacePeer,device] using resident,fun done=>done,fun nonempty=>nonempty⟩

theorem peek (pid : PeerId) : Preserves Inv (txPeekSource pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a first v b before run
  obtain ⟨d,p,queue,device,found,contents,_,after⟩ := txPeek_effect pid a b run
  rw [after]
  exact replace_peer before device found contents

theorem drop (pid : PeerId) : Preserves Inv (txDropSource pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  obtain ⟨d,p,device,found,_,after⟩ := txDrop_effect pid a b run
  rw [after]
  apply replace_subset before device found
  intro items member
  simp only [PrevQueue.all,PrevQueue.dropPeeked,Option.toList_none,List.nil_append] at member ⊢
  exact List.mem_append_right _ member

theorem complete (pid : PeerId) (items : List SkbId) (head : DataPacket) :
    Preserves Inv (txCompletionSource pid items head) := by
  unfold txCompletionSource
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch _ _) Inv)
  intro crypted
  split
  · exact wire (TxReservation.createDataDone_queues pid items) (createDataDone_cryptWire pid items)
  · exact preserves_pure _

theorem free_list (items : List SkbId) : Preserves Inv (TxDisposition.freeList items) := by
  induction items with
  | nil => exact preserves_pure _
  | cons id rest ih =>
    rw [TxDisposition.freeList_cons]
    exact preserves_bind (free_packet id) (fun _ => ih)

theorem dispose (pid : PeerId) (items : List SkbId) (key : KeypairId) :
    Preserves Inv (TxDisposition.disposeSource pid items key) := by
  have factor : TxDisposition.disposeSource pid items key = (do
      TxDisposition.freeList items
      keypairPut (some key) false
      peerPut (some pid)
      pure true) := by simp [TxDisposition.disposeSource,TxDisposition.freeList]
  rw [factor]
  exact preserves_bind (free_list items) fun _ =>
    preserves_bind (ReadyCiphertext.key_put (some key) false) fun _ =>
      preserves_bind (ReadyCiphertext.peer_put (some pid)) fun _ => preserves_pure _

theorem ready_tail (before : Inv w) (a b : Ambient)
    (run : ((txReadyTail pid first).run w).run a = .ok ((result,v),b)) : Inv v := by
  cases first with
  | none => simp only [txReadyTail] at run; cases run
  | some items =>
    cases headId : items.head? with
    | none => simp only [txReadyTail,headId] at run; cases run
    | some id =>
      rw [txReadyTail_factor pid items id headId,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨head,u,c,readRun,tail⟩ := run
      obtain ⟨same,clock,_,_,_⟩ := Packets.getTxSkb_current id w u head a c readRun
      subst u
      subst c
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,dropped,e,dropRun,tail⟩ := tail
      have selected := (hoare_iff_run_ambient _ _ _).mp (drop pid) w a () dropped e before dropRun
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,completed,f,completeRun,disposeRun⟩ := tail
      have held := (hoare_iff_run_ambient _ _ _).mp (complete pid items head)
        dropped e () completed f selected completeRun
      exact (hoare_iff_run_ambient _ _ _).mp (dispose pid items head.keypair)
        completed f result v b held disposeRun

theorem body (before : Inv w) (a b : Ambient)
    (run : ((TxDisposition.bodySource pid first).run w).run a = .ok ((result,v),b)) : Inv v := by
  rw [tx_body_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,readRun,tail⟩ := run
  have same := (hoare_iff_run_ambient _ _ _).mp (ready_world_frame first (fun s => s = w))
    w a ready u c rfl readRun
  subst u
  cases ready with
  | false => simp only [Bool.not_false,ite_true] at tail; cases tail; exact before
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    exact ready_tail before c b tail

theorem step_inv (pid : PeerId) : Preserves Inv (txStep pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [txStep_peek_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,peekRun,bodyRun⟩ := run
  exact body ((hoare_iff_run_ambient _ _ _).mp (peek pid) w a first u c before peekRun) c b bodyRun

theorem step (pid : PeerId) : Preserves (Coherent locals active) (txStep pid) :=
  coherent_join (OccurrenceTx.step pid) (step_inv pid)

theorem iteration (pid : PeerId) : Preserves (fun w : World => Coherent locals active w.wg)
    (txIter pid (Env.condResched .txWorker)) := by
  let P := fun w : World => Coherent locals active w.wg
  have next : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product (Coherent locals active) _ (step pid)
  have need : Preserves P (Env.condResched .txWorker) :=
    Decrypt.product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [txIter,workerIter] using [next,need,ambient]

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Tx
