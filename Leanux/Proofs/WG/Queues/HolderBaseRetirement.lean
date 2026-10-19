import Leanux.Proofs.WG.Queues.HolderRetirement
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint

/-! The live base list is detached without releasing its stamped occurrences.
Other durable fields stay tied to the actual original removal source. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private def otherView (w : WGWorld) := (sendView w,(passiveView w).2,Leanux.Proofs.WG.Queues.RxCredits.handoffTxView w)

private def otherOf (s : WGStoreView × (PeerId → Option Peer)) :=
  (s.1.dev.map Device.sendWorkQueue,
    ((s.1.dev.map Device.clearWorkQueue).getD [],activeCursor s.1.nlSock7,activeCursor s.1.nlSock8),
    fun pid => (s.2 pid).map (fun p => p.txQueue.all))

private theorem clear_factor (w : WGWorld) : otherOf (AllowedIps.clearListView w) = otherView w := by
  unfold otherView Leanux.Proofs.WG.Queues.RxCredits.handoffTxView
  simp only [otherOf,AllowedIps.clearListView,sendView,passiveView,wgStoreView,
    Option.map_map,Option.map_bind,Function.comp_def]

private theorem listDel_other (id : NodeId) : SameView otherView (listDel id) :=
  (AllowedIps.listDel_clearListView id).of_factor otherOf otherView (fun w => (clear_factor w).symm)

private theorem read_other (pid : PeerId) : SameView otherView (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg otherView (getPeer_normal pid w v p a b run).1

private theorem device_other : SameView otherView getDev :=
  getDev_sameWGStore.of_factor (fun s => otherView {dev := s.dev,nlSock7 := s.nlSock7,nlSock8 := s.nlSock8}) _ (fun _ => rfl)

private theorem modify_other (f : Device → Device)
    (send : ∀ d,(f d).sendWorkQueue=d.sendWorkQueue)
    (clear : ∀ d,(f d).clearWorkQueue=d.clearWorkQueue)
    (tx : ∀ (d : Device) (pid : PeerId),((f d).peers[pid]?).map (fun p : Peer => p.txQueue.all) =
      (d.peers[pid]?).map (fun p : Peer => p.txQueue.all)) : SameView otherView (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  unfold otherView sendView passiveView Leanux.Proofs.WG.Queues.RxCredits.handoffTxView
  simp only [Option.map_map,Option.bind_map,Function.comp_def,send,clear]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext pid
  cases w.dev <;> simp only [Option.map_none,Option.bind_none,Option.bind_some,tx]

private theorem removeByPeer_other (pid : PeerId) : SameView otherView (removeByPeer pid) := by
  have node (id : NodeId) : SameView otherView (AllowedIps.removeNodeBody id) :=
    (removeNodeBody_sameNode id).of_factor
      (fun s : WGStoreView => otherView {dev := s.dev,nlSock7 := s.nlSock7,nlSock8 := s.nlSock8}) _
      (fun _ => by
        unfold otherView Leanux.Proofs.WG.Queues.RxCredits.handoffTxView
        simp only [sendView,passiveView,nodeView,wgStoreView,nodeDevice,
          Option.map_map,Option.bind_map,Function.comp_def])
  intro initial
  let P := fun w => otherView w=initial
  change Preserves P _
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep
  apply preserves_bind ((read_other pid).wp (fun s => s=initial))
  intro p
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .removeListEmpty p.allowedipsList.isEmpty) P)
  intro empty
  cases empty with
  | true => exact preserves_pure ()
  | false =>
    apply preserves_bind ((modify_other (fun d => {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq+1}}) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)).wp (fun s => s=initial))
    intro _
    apply preserves_bind
    · apply list_view_spec otherView (fun s => s=initial)
      intro id acc
      unfold AllowedIps.removeStep
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .removeListIter true) P)
      intro _
      exact preserves_bind ((listDel_other id).wp (fun s => s=initial)) (fun _ => (node id).wp (fun s => s=initial))
    · intro _
      exact preserves_bind (hoare_liftAmbient (AmbientM.branch .removeListIter false) P) (fun _ => preserves_pure ())

private theorem mark_other (pid : PeerId) : SameView otherView (do
    let p ← getPeer pid
    setPeer pid {p with isDead := true}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,c,getter,write⟩ := run
  obtain ⟨readEq,timeEq,d,hd,hp⟩ := getPeer_normal pid w read p a c getter
  subst read
  subst c
  cases write
  unfold otherView sendView passiveView Leanux.Proofs.WG.Queues.RxCredits.handoffTxView
  simp only [hd,Option.map_some,Option.bind_some]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext q
  by_cases eq : pid=q <;> simp_all [Std.TreeMap.getElem?_insert]

private theorem peerMakeDead_other (pid : PeerId) : SameView otherView (peerMakeDead pid) := by
  intro initial
  let P := fun w => otherView w=initial
  change Preserves P _
  unfold peerMakeDead
  apply preserves_bind ((modify_other (fun d => {d with peerList := d.peerList.filter (· != pid)}) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)).wp (fun s => s=initial))
  intro _
  apply preserves_bind ((removeByPeer_other pid).wp (fun s => s=initial))
  intro _
  apply preserves_bind (device_other.wp (fun s => s=initial))
  intro d
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid))) P)
  intro _
  apply preserves_bind ((modify_other (fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)).wp (fun s => s=initial))
  intro _
  exact (mark_other pid).wp (fun s => s=initial)

private theorem free_other : SameView otherView WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have fields := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w)) w a result v b rfl run
  have projected := congrArg otherOf fields
  unfold otherView Leanux.Proofs.WG.Queues.RxCredits.handoffTxView
  simpa only [otherOf,AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,
    AllowedIps.resetAllowedips,wgStoreView,sendView,passiveView,
    Option.map_map,Option.map_bind,Option.bind_map,Function.comp_def] using projected

def withoutBase (holders : DurableHolders) (rest : Reservations) : DurableHolders :=
  {holders with base := rest}

private theorem aligned_other {holders : DurableHolders} (hi : holders.Aligned w)
    (fields : otherView v=otherView w)
    (base : rest.map Owner.slot=(v.dev.map Device.peerList).getD []) :
    (holders.withoutBase rest).Aligned v := by
  have send := congrArg Prod.fst fields
  have clear := congrArg (fun s => s.2.1.1) fields
  have cursor7 := congrArg (fun s => s.2.1.2.1) fields
  have cursor8 := congrArg (fun s => s.2.1.2.2) fields
  have tx := congrArg (fun s => s.2.2) fields
  refine ⟨base,?_,hi.clear.trans clear.symm,?_,hi.cursor7.trans cursor7.symm,hi.cursor8.trans cursor8.symm⟩
  · intro d hd
    cases hw : w.dev with
    | none => simp [otherView,sendView,hd,hw] at send
    | some old =>
      have eq : d.sendWorkQueue=old.sendWorkQueue := by
        simpa only [otherView,sendView,hd,hw,Option.map_some,Option.some.injEq] using send
      exact eq.trans (hi.send old hw)
  · intro pid batches found
    have eq : Leanux.Proofs.WG.Queues.RxCredits.handoffTxView v = Leanux.Proofs.WG.Queues.RxCredits.handoffTxView w := tx
    exact hi.tx pid batches (by rw [←eq]; exact found)

/-- Detachment moves every matching base occurrence to explicit caller loans.
Repeated slots are retained with their original multiplicity. -/
theorem peerMakeDead_funded (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) :
    (holders.withoutBase (BaseRemoval.live holders.base pid)).Funded cs
      (BaseRemoval.detached holders.base pid ++ loans) v ∧ StableRx cs v := by
  have effect := BaseRemoval.peerMakeDead_normal pid w v a b run
  have other := (ProjectedAction.iff_run_ambient _ _ _).mp (peerMakeDead_other pid) w a () v b run
  have carrier := hi.carriers.view (congrArg Prod.fst effect.1)
  refine ⟨⟨aligned_other hi.aligned other ?_,WorkReservations.carrier_loans_perm carrier ?_⟩,
    stable.view (congrArg Prod.snd effect.1)⟩
  · rw [effect.2,BaseRemoval.live_slots,hi.aligned.base]
    cases w.dev <;> rfl
  · apply List.perm_iff_count.mpr
    intro o
    have eq := List.Perm.count_eq (BaseRemoval.partition holders.base pid) o
    simp only [List.count_append] at eq
    simp only [withoutBase,owners,List.count_append]
    omega


private theorem mark_saved_effect (dead : List PeerId) (w v : WGWorld) (a b : Ambient)
    (run : (((for pid in dead do
      _ ← branch .peerRemoveAllIter1 true
      peerMakeDead pid) : WG.M Unit).run w).run a = .ok (((),v),b)) :
    DecryptCarrier.decryptView v = DecryptCarrier.decryptView w ∧
      otherView v = otherView w ∧
      (v.dev.map Device.peerList).getD [] =
        ((w.dev.map Device.peerList).getD []).filter (fun pid => !dead.contains pid) := by
  induction dead generalizing w a with
  | nil =>
    simp only [List.forIn_nil] at run
    cases run
    refine ⟨rfl,rfl,?_⟩
    exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
  | cons pid dead ih =>
    have factor : (for q in pid :: dead do
        _ ← branch .peerRemoveAllIter1 true
        peerMakeDead q : WG.M Unit) = (do
        _ ← branch .peerRemoveAllIter1 true
        peerMakeDead pid
        for q in dead do
          _ ← branch .peerRemoveAllIter1 true
          peerMakeDead q) := by
      simp only [List.forIn_cons,bind_assoc,pure_bind]
    rw [factor,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨flag,read,c,decision,rest⟩ := run
    have same := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter1 true) (fun g => g=w))
      w a flag read c rfl decision
    subst read
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,marked,d,mark,rest⟩ := rest
    cases u
    have first := BaseRemoval.peerMakeDead_normal pid w marked c d mark
    have fields := (ProjectedAction.iff_run_ambient _ _ _).mp (peerMakeDead_other pid) w c () marked d mark
    obtain ⟨credit,others,list⟩ := ih marked d rest
    refine ⟨credit.trans first.1,others.trans fields,?_⟩
    rw [list,first.2]
    cases hw : w.dev with
    | none => simp
    | some dev =>
      simp only [Option.map_some,Option.getD_some,List.filter_filter,List.contains_cons]
      congr 1
      funext q
      simp only [Bool.not_or,bne_eq,Bool.and_comm]

/-- The first saved-list pass detaches every original base occurrence, retaining
its original order as loans for the later payment pass. -/
theorem saved_makeDead_funded {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : (((for pid in holders.base.map Owner.slot do
      _ ← branch .peerRemoveAllIter1 true
      peerMakeDead pid) : WG.M Unit).run w).run a = .ok (((),v),b)) :
    (holders.withoutBase []).Funded cs (holders.base ++ loans) v ∧ StableRx cs v := by
  obtain ⟨credit,fields,list⟩ := mark_saved_effect (holders.base.map Owner.slot) w v a b run
  have empty : (v.dev.map Device.peerList).getD [] = [] := by
    rw [list,←hi.aligned.base]
    exact List.filter_eq_nil_iff.mpr (by
      intro pid hp
      rw [List.contains_iff_mem.mpr hp]
      decide)
  refine ⟨⟨aligned_other hi.aligned fields (by simpa only [List.map_nil] using empty.symm),
    WorkReservations.carrier_loans_perm (hi.carriers.view (congrArg Prod.fst credit)) ?_⟩,
    stable.view (congrArg Prod.snd credit)⟩
  apply List.perm_iff_count.mpr
  intro o
  simp only [withoutBase,owners,List.count_append,List.count_nil]
  omega

/-- Clearing the trie and capturing the actual list changes no holder account. -/
theorem saved_entry_funded {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : (BaseRemoval.entry.run w).run a = .ok ((dead,v),b)) :
    dead = holders.base.map Owner.slot ∧ holders.Funded cs loans v ∧ StableRx cs v := by
  unfold BaseRemoval.entry at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,middle,c,clear,rest⟩ := run
  have first := (ProjectedAction.iff_run_ambient _ _ _).mp BaseRemoval.allowedipsFree_view w a u middle c clear
  have others := (ProjectedAction.iff_run_ambient _ _ _).mp free_other w a u middle c clear
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨d,read,e,getter,finish⟩ := rest
  obtain ⟨readEq,timeEq,hd⟩ := DecryptCarrier.getDev_current c e getter
  subst read
  subst e
  have final : (d.peerList = dead ∧ middle = v) ∧ c = b := by simpa using finish
  obtain ⟨⟨result,state⟩,time⟩ := final
  subst dead
  subst v
  subst b
  have list := congrArg Prod.snd first
  have credit := congrArg Prod.fst first
  change DecryptCarrier.decryptView middle = DecryptCarrier.decryptView w at credit
  change middle.dev.map Device.peerList = w.dev.map Device.peerList at list
  have base : holders.base.map Owner.slot=d.peerList := by
    have original := hi.aligned.base
    rw [←list,hd] at original
    exact original
  refine ⟨base.symm,⟨?_,hi.carriers.view (congrArg Prod.fst credit)⟩,
    stable.view (congrArg Prod.snd credit)⟩
  have aligned := aligned_other hi.aligned others (rest := holders.base) (by simpa only [hd,Option.map_some,Option.getD_some] using base)
  exact aligned


/-- The actual bulk-removal call preserves complete funding, paying every saved
base occurrence once. Work flushed during removal can shorten its work lists. -/
theorem peerRemoveAll_funded {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : (peerRemoveAll.run w).run a = .ok (((),v),b)) :
    DuringWork (holders.withoutBase []) cs loans v := by
  rw [BaseRemoval.peerRemoveAll_entry,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨dead,entered,c,entry,rest⟩ := run
  obtain ⟨saved,funded,stable⟩ := saved_entry_funded hi stable a c entry
  subst dead
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,marked,d,mark,rest⟩ := rest
  cases u
  obtain ⟨detached,stable⟩ := saved_makeDead_funded (v := marked) funded stable c d (by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨PUnit.unit,marked,d,mark,rfl⟩)
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨flag,read,e,decision,rest⟩ := rest
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter1 false) (fun g => g=marked))
    marked d flag read e rfl decision
  subst read
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,paid,f,payment,rest⟩ := rest
  cases u
  have finished := saved_afterDead_normal (v := paid) holders.base (duringWork_initial detached stable) e f (by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨PUnit.unit,paid,f,payment,rfl⟩)
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨last,read,g,decision,rest⟩ := rest
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter2 false) (fun state => state=paid))
    paid f last read g rfl decision
  subst read
  cases rest
  exact finished


theorem peerRemoveAll_observed_funded {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (h : List LifetimeEvent) (a b : Ambient)
    (run : (runStatePrefix peerRemoveAllPrefix w a h).1 = .ok (((),v),b)) :
    DuringWork (holders.withoutBase []) cs loans v :=
  peerRemoveAll_funded hi stable a b ((peerRemoveAllPrefix_erases w a h).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
