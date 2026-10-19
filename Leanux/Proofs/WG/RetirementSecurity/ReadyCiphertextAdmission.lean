import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextFrames

/-! A freshly held batch is disjoint from old queued batches. Original
admission resets its head before queue installation; even ring refusal cannot
install a ready batch with unwritten members. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem enqueue (before : Inv w)
    (physical : TxInventory (⟨.unpublished,pid,items⟩::locals) w) (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a=.ok ((ret,v),b)) : Inv v := by
  have previous (other : PeerId) (p : Peer) (found : peerAt w other=some p)
      (batch : List SkbId) (member : batch∈p.txQueue.all) (first : SkbId)
      (head : batch.head?=some first) (crypted : TxDisposition.HeadState first .crypted v) : Complete batch v := by
    have outside : ∀id∈batch,id∉items := by
      intro id inside fresh
      exact physical.localsSeparate other p found id (by simp [txLocalItems,fresh])
        (List.mem_flatten.mpr ⟨batch,member,inside⟩)
    have same (id : SkbId) (inside : id∈batch) : TxDisposition.txPackets v id=TxDisposition.txPackets w id :=
      (ProjectedAction.iff_run_ambient _ _ _).mp (TxDisposition.MarkTransport.enqueue_other id pid items (outside id inside))
        w a ret v b run
    have oldHead : TxDisposition.HeadState first .crypted w := by
      obtain ⟨packet,stored,mark⟩:=crypted
      exact ⟨packet,same first (List.mem_of_head? head) ▸ stored,mark⟩
    have complete:=before other p found batch member first head oldHead
    intro id inside
    exact (complete id inside).frame (same id inside)
  intro other p found batch member first head crypted
  have point:handoffTxView v other=some p.txQueue.all:=by
    simpa [handoffTxView,peerAt] using congrArg (Option.map (fun p=>p.txQueue.all)) found
  rcases enqueue_queue_effect pid items a b run with ⟨_,same⟩ | ⟨_,_,effect⟩
  · rw [same] at point
    obtain ⟨old,resident,queue⟩:=Option.map_eq_some_iff.mp point
    exact previous other old resident batch (queue.symm ▸ member) first head crypted
  · rw [effect other] at point
    obtain ⟨batches,prior,queue⟩:=Option.map_eq_some_iff.mp point
    obtain ⟨old,resident,oldQueue⟩:=Option.map_eq_some_iff.mp prior
    rcases List.mem_append.mp (queue.symm ▸ member) with oldBatch | newBatch
    · exact previous other old resident batch (oldQueue.symm ▸ oldBatch) first head crypted
    · by_cases same:other=pid
      · subst other
        simp only [ite_true,List.mem_singleton] at newBatch
        subst batch
        obtain ⟨packet,stored⟩:=physical.localResident first (by simp [txLocalItems,List.mem_of_head? head])
        obtain ⟨q,uncrypted,mark⟩:=enqueue_head_uncrypted head stored pid a b run
        obtain ⟨r,ready,done⟩:=crypted
        have eq:q=r:=Option.some.inj (uncrypted.symm.trans ready)
        have impossible:PacketState.uncrypted=.crypted:=mark.symm.trans (eq ▸ done)
        cases impossible
      · simp only [same,ite_false,List.not_mem_nil] at newBatch

theorem create_publish (before : Inv w) (items : List SkbId) (ret : Int) (a b : Ambient)
    (run : ((createPublishReturn items ret).run w).run a=.ok ((result,v),b)) : Inv v := by
  have proof : Preserves Inv (createPublishReturn items ret) := by
    have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) := hoare_liftAmbient a Inv
    have publish := publish_not_ready items .dead (by decide)
    routing_tx_source [createPublishReturn] using [publish,ambient]
  exact (hoare_iff_run_ambient _ _ _).mp proof w a result v b before run

theorem create_return (before : Inv w)
    (physical : TxInventory (⟨.unpublished,pid,items⟩::locals) w) (a b : Ambient)
    (run : ((createReturnSource pid items).run w).run a=.ok ((ret,v),b)) : Inv v := by
  simp only [createReturnSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,dead,t,e,branchRun,tail⟩:=run
  obtain ⟨same,clock,_,_,_⟩:=Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have same:t=w:=by cases branchRun; rfl
  subst t
  cases dead with
  | true=>simp only [ite_true] at tail; cases tail; exact before
  | false=>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨result,u,c,enqueueRun,publishRun⟩:=tail
    exact create_publish (enqueue before physical e c enqueueRun) items result c b publishRun

theorem cleanup (pid first : SkbId) (items : List SkbId) :
    Preserves Inv (TxDisposition.cleanupSource pid items first) := by
  unfold TxDisposition.cleanupSource
  exact hoare_bind _ _ (read_packet first) fun packet=>hoare_bind _ _ (key_put (some packet.keypair) false)
    fun _=>hoare_bind _ _ (peer_put (some pid)) fun _=>free_list items

theorem create_tail (pid first : SkbId) (items : List SkbId) (ret : Int) :
    Preserves Inv (TxDisposition.createTailSource pid items first ret) := by
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) := hoare_liftAmbient a Inv
  routing_tx_source [TxDisposition.createTailSource] using [cleanup,ambient]

/-- Original createData preserves ready-byte coherence across peer refusal,
queue refusal, ring refusal and successful ring publication. -/
theorem create (before : Inv w)
    (physical : TxInventory (⟨.unpublished,pid,items⟩::locals) w) (a b : Ambient)
    (run : ((createData pid items).run w).run a=.ok (((),v),b)) : Inv v := by
  have factor:createData pid items=(do
      let some first:=items.head? | invariant "an empty ring item"
      let ret←createReturnSource pid items
      TxDisposition.createTailSource pid items first ret):=by
    simp only [TxDisposition.createSource_factor,createReturnSource,createPublishReturn,
      bind_assoc,bind_if_source,pure_bind]
    rfl
  rw [factor] at run
  cases head:items.head? with
  | none=>simp only [head] at run; cases run
  | some first=>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨ret,u,c,front,tail⟩:=run
    exact (hoare_iff_run_ambient _ _ _).mp (create_tail pid first items ret) u c () v b
      (create_return before physical a c front) tail

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
