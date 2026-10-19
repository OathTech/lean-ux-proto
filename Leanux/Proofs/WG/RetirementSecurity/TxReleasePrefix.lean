import Leanux.Proofs.WG.RetirementSecurity.TxDispositionCoverage

/-! Exact post-allocation free-loop accounting. The released prefix is
identified by the original successful free calls; a Stop retains the remaining
caller-local suffix and the actual failing getter, not a fabricated final world. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxReleasePrefix
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def observed (items : List SkbId) : TxDisposition.Obs Unit := do
  for id in items do TxDisposition.nativeAccess (freeTxSkbPrefix id)

def events (w : WGWorld) (items : List SkbId) : List TxDisposition.Event :=
  items.flatMap fun id=>[.access (.packet (.read (.inl id) (packetStamp w id))),
    .access (.packet (.release (.inl id) (packetStamp w id)))]

theorem cons (id : SkbId) (rest : List SkbId) : observed (id::rest)=(do
    TxDisposition.nativeAccess (freeTxSkbPrefix id)
    observed rest) := by
  simp [observed]

theorem erases (items : List SkbId) :
    ErasesPrefix (observed items) (liftWG (TxDisposition.freeList items)) := by
  induction items with
  | nil=>exact erasesPrefix_pure ()
  | cons id rest ih=>
    rw [cons,TxDisposition.freeList_cons,liftWG_bind]
    exact erasesPrefix_bind (TxDisposition.nativeAccess_erases (freeTxSkbPrefix_erases id)) (fun _=>ih)

def Account (w : World) (items : List SkbId) (h : List TxDisposition.Event)
    (result : Except Stop (Unit×World)) (journal : List TxDisposition.Event) : Prop :=
  ∃done rest v,items=done++rest ∧
    (liftWG (TxDisposition.freeList done)).run w=.ok ((),v) ∧
    journal=h++events w.wg done ∧
    match result with
    | .ok (_,out)=>rest=[] ∧ out=v
    | .error reason=>∃id tail,rest=id::tail ∧ (liftWG (getTxSkb id)).run v=.error reason

private theorem one (id : SkbId) (w : World) (h : List TxDisposition.Event) :
    (∃reason,runPrefix (TxDisposition.nativeAccess (freeTxSkbPrefix id)) w h=(.error reason,h) ∧
      (liftWG (getTxSkb id)).run w=.error reason) ∨
    (∃v,runPrefix (TxDisposition.nativeAccess (freeTxSkbPrefix id)) w h=
      (.ok ((),v),h++events w.wg [id]) ∧
      (liftWG (freeTxSkb id)).run w=.ok ((),v) ∧
      (∀other,packetStamp v.wg other=packetStamp w.wg other)) := by
  rw [TxDisposition.free_run]
  cases run : ((getTxSkb id).run w.wg).run w.ambient with
  | error reason=>
    left
    exact ⟨reason,by simp [liftWG_run,run,Except.map],by simp [liftWG_run,run,Except.map]⟩
  | ok out=>
    obtain ⟨⟨packet,v⟩,b⟩:=out
    obtain ⟨rfl,rfl,d,device,stored⟩:=Packets.getTxSkb_current id w.wg v packet w.ambient b run
    let v : World:={w with wg:=Packets.update w.wg fun d=>{d with txSkbs:=d.txSkbs.erase id}}
    have freed : (liftWG (freeTxSkb id)).run w=.ok ((),v) := by
      simp only [liftWG_run,Packets.freeTxSkb_run w.wg w.ambient d id packet device stored,Except.map]
      rfl
    right
    refine ⟨v,?_,freed,?_⟩
    · simp only [liftWG_run,run,Except.map]
      simpa only [liftWG_run,Except.map,events,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
        congrArg (fun result=>(result,h++events w.wg [id])) freed
    · intro other
      simp [v,packetStamp,Packets.update,Option.map_map,Function.comp_def]

/-- Each observation is exactly a successfully freed prefix and the residual
input suffix. A stopped suffix begins at its original failed getter; no release
is credited to that getter or to later entries. -/
theorem account (items : List SkbId) (w : World) (h : List TxDisposition.Event) :
    Account w items h (runPrefix (observed items) w h).1 (runPrefix (observed items) w h).2 := by
  induction items generalizing w h with
  | nil=>exact ⟨[],[],w,rfl,rfl,by simp [observed,events],rfl,rfl⟩
  | cons id rest ih=>
    rw [cons,runPrefix_bind]
    rcases one id w h with ⟨reason,stopped,getter⟩ | ⟨v,returned,freed,stamps⟩
    · rw [stopped]
      exact ⟨[],id::rest,w,rfl,rfl,by simp [events],id,rest,rfl,getter⟩
    · rw [returned]
      obtain ⟨done,left,u,split,prior,journal,finish⟩:=ih v (h++events w.wg [id])
      refine ⟨id::done,left,u,by simp only [List.cons_append,split],?_,?_,finish⟩
      · rw [TxDisposition.freeList_cons,liftWG_bind,StateT.run_bind,freed]
        exact prior
      · have same : events v.wg done=events w.wg done := by
          unfold events
          congr 1
          funext other
          rw [stamps]
        rw [same] at journal
        simpa only [events,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using journal

theorem normal (items : List SkbId) (w v : World) (h k : List TxDisposition.Event)
    (run : runPrefix (observed items) w h=(.ok ((),v),k)) :
    (liftWG (TxDisposition.freeList items)).run w=.ok ((),v) ∧ k=h++events w.wg items := by
  have accounting:=account items w h
  rw [run] at accounting
  obtain ⟨done,left,u,split,prior,journal,empty,same⟩:=accounting
  subst left
  simp only [List.append_nil] at split
  subst items
  subst u
  exact ⟨prior,journal⟩

theorem stopped (items : List SkbId) (w : World) (h k : List TxDisposition.Event)
    (run : runPrefix (observed items) w h=(.error reason,k)) :
    ∃done id rest v,items=done++id::rest ∧
      (liftWG (TxDisposition.freeList done)).run w=.ok ((),v) ∧
      k=h++events w.wg done ∧ (liftWG (getTxSkb id)).run v=.error reason := by
  have accounting:=account items w h
  rw [run] at accounting
  obtain ⟨done,left,v,split,prior,journal,id,rest,equal,getter⟩:=accounting
  exact ⟨done,id,rest,v,by simpa only [equal] using split,prior,journal,getter⟩

/-- The original free loop is total on a distinct resident batch. This is a
local precondition, supplied by initialized ownership at the worker selection;
it does not promise that earlier key/peer cleanup payments return. -/
theorem total (items : List SkbId) (unique : items.Nodup)
    (resident : ∀id∈items,∃packet,TxDisposition.txPackets w id=some packet) (a : Ambient) :
    ∃v,((TxDisposition.freeList items).run w).run a=.ok (((),v),a) := by
  induction items generalizing w with
  | nil=>exact ⟨w,rfl⟩
  | cons id rest ih=>
    obtain ⟨absent,distinct⟩:=List.nodup_cons.mp unique
    obtain ⟨packet,found⟩:=resident id (by simp)
    obtain ⟨d,device,stored⟩:=Option.bind_eq_some_iff.mp found
    let v:=Packets.update w fun d=>{d with txSkbs:=d.txSkbs.erase id}
    have freed : ((freeTxSkb id).run w).run a=.ok (((),v),a) :=
      Packets.freeTxSkb_run w a d id packet device stored
    have cells:TxDisposition.txPackets v=fun other=>if id=other then none else TxDisposition.txPackets w other :=
      (hoare_iff_run_ambient _ _ _).mp (TxDisposition.free_packet_wp id (TxDisposition.txPackets w))
        w a () v a rfl freed
    have remaining:∀other∈rest,∃packet,TxDisposition.txPackets v other=some packet := by
      intro other member
      obtain ⟨p,found⟩:=resident other (by simp [member])
      have different:id≠other := by intro equal; subst other; exact absent member
      exact ⟨p,by simpa only [cells,different,ite_false] using found⟩
    obtain ⟨u,tail⟩:=ih distinct remaining
    refine ⟨u,?_⟩
    rw [TxDisposition.freeList_cons,MaterialOrigin.bind_ok_ambient]
    exact ⟨(),v,a,freed,tail⟩

/-- Both original owners use this same observed free loop: refusal cleanup
after its two payments, and TX disposal before its two payments. -/
theorem cleanup_factor (pid : PeerId) (items : List SkbId) (first : SkbId) :
    TxDisposition.cleanup pid items first=(do
      TxDisposition.nativeAccess (keypairPutPrefix
        (some (←TxDisposition.nativeAccess (getTxSkbPrefix first)).keypair) false)
      TxDisposition.nativeAccess (peerPutMixed (some pid))
      observed items) := rfl

theorem dispose_factor (pid : PeerId) (items : List SkbId) (kid : KeypairId) :
    TxDisposition.dispose pid items kid=(do
      observed items
      TxDisposition.nativeAccess (keypairPutPrefix (some kid) false)
      TxDisposition.nativeAccess (peerPutMixed (some pid))
      pure true) := by
  simp only [TxDisposition.dispose,observed,bind_assoc,pure_bind]

end Leanux.Proofs.WG.RetirementSecurity.TxReleasePrefix
