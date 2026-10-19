import Leanux.Proofs.WG.Config.ReplacementCompletionFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.ReplaceCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Queues.RxCredits Queues.RxCredits.DurableHolders AllowedIps Std.Do Lifetimes

theorem funded_empty (holders : DurableHolders) (cs : Ledger) (loans : Reservations)
    (v : WGWorld) (after : DuringWork (holders.withoutBase []) cs loans v) :
    (v.dev.map Device.peerList).getD [] = [] := by
  obtain ⟨remaining,work,funded,_⟩ := after
  rw [←funded.aligned.base,work.base]
  rfl

theorem removeAll_empty (holders : DurableHolders) (cs : Ledger) (loans : Reservations)
    (initial : FlatTable × FlatTable) (w v : WGWorld) (a b : Ambient)
    (funded : holders.Funded cs loans w) (stable : StableRx cs w)
    (base : BaseCoherence.Inv w) (routing : RoutedView (routingView w) initial)
    (run : (peerRemoveAll.run w).run a = .ok (((),v),b)) :
    ∃ d, v.dev = some d ∧ d.peerList = [] ∧ d.peerHashtable = [] ∧
      RoutedView (routingView v) ([],[]) := by
  have after := DurableHolders.peerRemoveAll_funded funded stable a b run
  have empty := funded_empty holders cs loans v after
  have coherent := (hoare_iff_run_ambient _ _ _).mp
    BaseCoherence.peerRemoveAll_preserves w a () v b base run
  have start : CompletionState initial [] w := ⟨.nil,routing⟩
  obtain ⟨suffix,append,safe,post⟩ :=
    Configuration.peerRemoveAllObserved_empty_spec initial w a [] start
  have erase := Configuration.peerRemoveAllObserved_erases w a []
  change (runPrefix (Configuration.peerRemoveAllObserved.run w) a []).1 = _ at erase
  have outcome : (runPrefix (Configuration.peerRemoveAllObserved.run w) a []).1 =
      .ok (((),v),b) := erase.trans run
  rw [outcome] at post
  have routed : RoutedView (routingView v) ([],[]) := by
    simpa only [post.2] using post.1.2
  obtain ⟨d,t4,t6,device,_,_,_⟩ := routed.realize
  have list : d.peerList = [] := by simpa only [device,Option.map_some,Option.getD_some] using empty
  refine ⟨d,device,list,?_,routed⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row member
  have bad := coherent.2 row (by simpa only [BaseCoherence.rows,device,Option.map_some,Option.getD_some] using member)
  simp only [BaseCoherence.slots,device,Option.map_some,Option.getD_some,list,List.not_mem_nil] at bad


private abbrev reqPrefix := noise_const _private.Leanux.Proofs.WG.Config.ReplacePeersRequestSource.«0».Leanux.Proofs.WG.Config.replacePeersPrefix
private abbrev suffix := noise_const _private.Leanux.Proofs.WG.Config.ReplacePeersRequestSource.«0».Leanux.Proofs.WG.Config.replacePeersSuffix

theorem prefix_state (d : Device) (w : WGWorld) (a : Ambient)
    (result : Except Int Unit) (v : WGWorld) (b : Ambient)
    (pre : w.dev=some d ∧ selectsDevice w d)
    (run : ((reqPrefix (byIndex d)).run w).run a = .ok ((result,v),b)) :
    result=.ok () ∧ v=generated w := by
  obtain ⟨ret,current,c,actual,resultEq,device⟩ :=
    ((returns_iff _ _ _).mpr (lookupInterface_index d)) w a pre
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (lookupInterface_sameWGWorld (byIndex d)) w a ret current c actual
  change current=w at same
  subst current
  subst ret
  change (((lookupInterface (byIndex d)).run w).run a >>= fun ((found,state),time) => _) = _ at run
  rw [actual] at run
  simp [branch,AmbientM.branch,modifyDev] at run
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
  exact ⟨rfl,rfl⟩

theorem lift_injective {α : Type} (left right : WG.M α)
    (same : liftWG left = liftWG right) : left=right := by
  funext w a
  let product : World := {ambient := a,tasks := Runner.initialTasks 0,fs := Runner.initialFS,wg := w}
  have both := congrFun same product
  change (liftWG left).run product = (liftWG right).run product at both
  rw [liftWG_run,liftWG_run] at both
  have projected := congrArg (Except.map (fun out : α × World => ((out.1,out.2.wg),out.2.ambient))) both
  cases leftRun : left w a <;> cases rightRun : right w a <;>
    simpa only [product,StateT.run,leftRun,rightRun,Except.map] using projected

theorem native_source (selector : DeviceRef) :
    wgSetDevice (replacePeersAttrs selector) = (do
      let selected ← reqPrefix selector
      match selected with
      | .error e => return e
      | .ok () => peerRemoveAll; suffix) := by
  apply lift_injective
  rw [←replacePeersWith_source]
  simp only [replacePeersWith,liftWG_bind,bind_assoc]
  congr 1
  funext selected
  cases selected with
  | error e => simp only [liftWG_pure,pure_bind]
  | ok u => cases u; simp only [liftWG_bind,bind_assoc,pure_bind,bind_pure]



theorem request_empty (cs : Ledger) (loans : Reservations)
    (tables : FlatTable × FlatTable) (d : Device) :
    Noise.Ensures (wgSetDevice (replacePeersAttrs (byIndex d)))
      (fun w => w.dev=some d ∧ selectsDevice w d ∧ Input cs loans tables w)
      (fun result v => result=0 ∧ Empty v) := by
  intro w a result v b pre run
  rw [native_source,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨selected,entry,c,front,tail⟩ := run
  obtain ⟨rfl,rfl⟩ := prefix_state d w a selected entry c ⟨pre.1,pre.2.1⟩ front
  obtain ⟨⟨holders,funded,stable⟩,base,routing⟩ := pre.2.2
  change ((peerRemoveAll >>= fun _ => suffix).run (generated w)).run c = _ at tail
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨u,removed,time,removal,finish⟩ := tail
  cases u
  have empty := removeAll_empty holders cs loans tables (generated w) removed c time
    (generation_funded holders cs loans w funded) (generation_stable cs w stable)
    (generation_base w base) (generation_routed w tables routing) removal
  change ((do
    _ ← branch .setDevHasPrivateKey false
    _ ← branch .setDevHasPeers false
    _ ← branch .setDevZeroKey false
    pure (0 : Int) : WG.M Int).run removed).run time = _ at finish
  simp only [branch,AmbientM.branch] at finish
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := finish
  exact ⟨rfl,empty⟩

end Leanux.Proofs.WG.Config.ReplaceCompletion
