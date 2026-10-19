import Leanux.Proofs.WG.Packets.PublicationHistory

namespace Leanux.Proofs.WG.PublicationHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationIdentity

/-- The selected cell may be replaced. Every other packet, the device epoch,
and all resident peer identities remain visible. -/
def around (id : SkbId) (w : WGWorld) :=
  ((RxDisposition.nativeRxStore w).1,
    (fun slot : SkbId => if slot = id then none else (RxDisposition.nativeRxStore w).2 slot),
    CurrentIdentity.peerView w)

private theorem around_of_full (id : SkbId)
    (packets : RxDisposition.nativeRxStore v = RxDisposition.nativeRxStore w)
    (peers : CurrentIdentity.peerView v = CurrentIdentity.peerView w) : around id v = around id w := by
  simp only [around,packets,peers]

/-- Both decrypt outcomes retain packets and peer identity. Rejection may
still invalidate the receiving key, and no final state is asserted for Stop. -/
theorem readDecrypt_views (id : SkbId) (w v : WGWorld) (a b : Ambient)
    (result : RxPacket × Option RxPacket)
    (hr : ((RxOrigin.readDecrypt id).run w).run a = .ok ((result,v),b)) :
    RxDisposition.nativeRxStore v = RxDisposition.nativeRxStore w ∧
      CurrentIdentity.peerView v = CurrentIdentity.peerView w := by
  simp only [RxOrigin.readDecrypt,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨pkt,read,readAmbient,hread,decrypted,after,afterAmbient,run,done⟩ := hr
  obtain ⟨readEq,ambientEq,_,_,_⟩ := Packets.getRxSkb_current id w read pkt a readAmbient hread
  subst read
  subst readAmbient
  cases done
  constructor
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDecrypt.«0».Leanux.Proofs.WG.OwnerDecrypt.decryptPacket_rx) pkt)
      w a decrypted v b run
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (CurrentIdentity.peerView_of_configured
        ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.decryptPacket_view) pkt))
      w a decrypted v b run

/-- Actual publication changes the selected packet state and increments its
peer reference, without changing any peer allocation stamp or static key. -/
theorem publish_around (id : SkbId) (state : PacketState) :
    SameView (around id) (RxWorkers.publishSource id state) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a pid v b hr
  obtain ⟨d,pkt,key,p,hd,hpkt,hkey,word,hpeer,effect⟩ := publish_execution id state w v a b pid hr
  have hv := congrArg WGStoreView.dev effect
  change v.dev = some _ at hv
  unfold around RxDisposition.nativeRxStore CurrentIdentity.peerView
  simp only [hv,hd,Option.map_some,Option.bind_some,Prod.mk.injEq]
  refine ⟨True.intro,?_,?_⟩
  · funext slot
    by_cases same : slot = id
    · simp only [same,ite_true]
    · simp [Std.TreeMap.getElem?_insert,Ne.symm same]
  · apply congrArg some
    funext slot
    by_cases same : slot = pid
    · subst slot
      simp [hpeer,CurrentIdentity.identity]
    · simp [Std.TreeMap.getElem?_insert,Ne.symm same]

private theorem setRx_around (id : SkbId) (f : RxPacket → RxPacket) :
    SameView (around id) (setRxSkb id f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have raw := hr
  unfold setRxSkb at raw
  rw [liftSkb_run] at raw
  cases hd : w.dev with
  | none => simp [hd] at raw
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none =>
      simp [hd,SkbStore.setRx,SkbStore.getRx,hp,invariant,AmbientM.invariant] at raw
      cases raw
    | some pkt =>
      have run := Packets.setRxSkb_run w a d id pkt f hd hp
      rw [run] at hr
      cases hr
      unfold around RxDisposition.nativeRxStore CurrentIdentity.peerView Packets.update
      simp only [hd,Option.map_some,Option.bind_some,Prod.mk.injEq]
      refine ⟨True.intro,?_,True.intro⟩
      funext slot
      by_cases same : slot = id
      · simp only [same,ite_true]
      · simp [Std.TreeMap.getElem?_insert,Ne.symm same]

theorem finish_around (id : SkbId) (pair : RxPacket × Option RxPacket) :
    SameView (around id) (finish id pair) := by
  intro initial
  change Preserves (fun w => around id w = initial) _
  unfold finish finishWith
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decWorkerDecrypted pair.2.isSome) _)
  intro recorded
  cases recorded with
  | false => exact (publish_around id .dead).wp (fun s => s = initial)
  | true =>
    simp only [↓reduceIte]
    cases pair.2 with
    | none => exact hoare_liftAmbient (AmbientM.invariant "unreachable") _
    | some out =>
      exact preserves_bind ((setRx_around id (fun _ => out)).wp (fun s => s = initial))
        (fun _ => (publish_around id .crypted).wp (fun s => s = initial))

/-- A normal failed decrypt publishes DEAD, so that selected cell does not
acquire an authorization obligation. -/
theorem finish_none_dead (id : SkbId) (pkt : RxPacket) (w v : WGWorld) (a b : Ambient) (pid : PeerId)
    (hr : ((finish id (pkt,none)).run w).run a = .ok ((pid,v),b)) :
    ∃ final, (RxDisposition.nativeRxStore v).2 id = some final ∧ final.state = .dead := by
  unfold finish finishWith at hr
  simp only [Option.isSome_none,branch,StateT.run_monadLift,monadLift_self,
    StateT.run_bind,StateT.run_pure,CounterWindow.except_pure,CounterWindow.branch_run,
    CounterWindow.except_ok_bind,Bool.false_eq_true,↓reduceIte] at hr
  obtain ⟨d,packet,key,p,hd,hpkt,hkey,word,hpeer,effect⟩ := publish_execution id .dead w v
    (CounterWindow.record a .decWorkerDecrypted false) b pid hr
  have hv := congrArg WGStoreView.dev effect
  change v.dev = some _ at hv
  refine ⟨{packet with state := .dead},?_,rfl⟩
  simp [RxDisposition.nativeRxStore,hv]

/-- Exact selected prepare also provides the frame for every other live
packet and distinguishes successful publication from DEAD publication. -/
theorem native_prepare_selected (w v : WGWorld) (a b : Ambient)
    (h t : List (MaterialOrigin.Event RxOrigin.Receipt)) (pid : PeerId)
    (hr : runWGPrefix RxOrigin.prepare w a h = (.ok ((some pid,v),b),t)) :
    ∃ id, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ pre tail,
      r.Valid (RxOrigin.readDecrypt id) ∧
      t = h ++ pre ++ .receipt (.decrypt id r) :: tail ∧
      around id v = around id w ∧
      (r.value.2 = none → ∃ pkt, (RxDisposition.nativeRxStore v).2 id = some pkt ∧ pkt.state = .dead) ∧
      (∀ out, r.value.2 = some out → Published id r out pid v b) := by
  obtain ⟨d,id,ring,hd,queue,selectedRun⟩ := prepare_selected w v a b h t pid hr
  obtain ⟨r,before,tail,entry,ambientEntry,valid,read,finishRun,position,published⟩ :=
    selected_receipt id _ v _ b h t pid selectedRun
  obtain ⟨pre,hprefix⟩ := StateAppends.focus MaterialOrigin.Event.life MaterialOrigin.life?
    (RxOrigin.readDecryptPrefix id) (Packets.update w (fun d => {d with decryptQueue := ring}))
      (CounterWindow.record a .decWorkerConsumed true) h
  change (runWGPrefix (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id))
    _ _ h).2 = h ++ pre at hprefix
  rw [read] at hprefix
  change before = h ++ pre at hprefix
  have finishSource := (finish_erases id r.value r.after r.ambientAfter _).symm.trans
    (congrArg Prod.fst finishRun)
  have decryptFrame := readDecrypt_views id r.before r.after r.ambientBefore r.ambientAfter r.value valid
  have finalFrame := (ProjectedAction.iff_run_ambient _ _ _).mp (finish_around id r.value)
    r.after r.ambientAfter pid v b finishSource
  have initialFrame : around id r.before = around id w := by
    rw [entry]
    simp only [around,RxDisposition.nativeRxStore,CurrentIdentity.peerView,Packets.update,
      Option.map_map,Option.bind_map,Function.comp_def]
  refine ⟨id,r,pre,tail,valid,?_,finalFrame.trans ((around_of_full id decryptFrame.1 decryptFrame.2).trans initialFrame),?_,published⟩
  · simpa only [hprefix,List.append_assoc,List.singleton_append] using position
  · intro noneResult
    have shape : r.value = (r.value.1,none) := Prod.ext rfl noneResult
    rw [shape] at finishSource
    exact finish_none_dead id r.value.1 r.after v r.ambientAfter b pid finishSource

/-- The empty queue arm records its branch but emits no journal entry and
leaves the whole native WG state unchanged. -/
theorem native_prepare_none (w v : WGWorld) (a b : Ambient)
    (h t : List (MaterialOrigin.Event RxOrigin.Receipt))
    (hr : runWGPrefix RxOrigin.prepare w a h = (.ok ((none,v),b),t)) : v = w ∧ t = h := by
  change runStatePrefix RxOrigin.prepare w a h = _ at hr
  rw [prepare_factor,runStatePrefix_bind] at hr
  simp only [liftWGPrefix,runStatePrefix_lift] at hr
  cases hd : w.dev with
  | none =>
    simp [getDev,hd,invariant,AmbientM.invariant] at hr
    cases hr
  | some d =>
    have hget : (getDev.run w).run a = .ok ((d,w),a) := by simp [getDev,hd]
    rw [hget] at hr
    cases queue : d.decryptQueue.consume with
    | mk item ring =>
      cases item with
      | none =>
        simp only [queue,runStatePrefix_bind,runStatePrefix_lift,branch,StateT.run_monadLift,
          monadLift_self,StateT.run_bind,StateT.run_pure,CounterWindow.except_pure,
          CounterWindow.branch_run,CounterWindow.except_ok_bind,runStatePrefix_pure,
          Prod.mk.injEq,Except.ok.injEq] at hr
        exact ⟨hr.1.1.2.symm,hr.2.symm⟩
      | some id =>
        simp only [queue,runStatePrefix_bind,runStatePrefix_lift,branch,StateT.run_monadLift,
          monadLift_self,StateT.run_bind,StateT.run_pure,CounterWindow.except_pure,
          CounterWindow.branch_run,CounterWindow.except_ok_bind] at hr
        have hm : ((modifyDev (fun d => {d with decryptQueue := ring})).run w).run
            (CounterWindow.record a .decWorkerConsumed true) = .ok
            (((),Packets.update w (fun d => {d with decryptQueue := ring})),
              CounterWindow.record a .decWorkerConsumed true) := rfl
        rw [hm] at hr
        cases run : runStatePrefix (selected id) (Packets.update w (fun d => {d with decryptQueue := ring}))
            (CounterWindow.record a .decWorkerConsumed true) h with
        | mk result journal =>
          cases result with
          | error e => simp [run] at hr
          | ok result =>
            rcases result with ⟨⟨pid,g⟩,ambient⟩
            simp [run,runStatePrefix_pure] at hr

/-- A frame around the selected slot transports each other packet's fixed
publication occurrence and certificate. -/
theorem Anchored.around {id slot : SkbId} (hi : Anchored h slot w) (different : slot ≠ id)
    (same : around id v = around id w) : Anchored h slot v := by
  have epoch := congrArg Prod.fst same
  have packet := congrFun (congrArg (fun s => s.2.1) same) slot
  have peers := congrArg (fun s => s.2.2) same
  change CurrentIdentity.peerView v = CurrentIdentity.peerView w at peers
  change (if slot = id then none else (RxDisposition.nativeRxStore v).2 slot) =
    (if slot = id then none else (RxDisposition.nativeRxStore w).2 slot) at packet
  apply hi.transport
  · exact congrArg (fun epoch : Option Nat => (epoch.getD 0,slot+1)) epoch
  · simpa only [different,ite_false] using packet
  · intro pid d p hd hp
    have old : (CurrentIdentity.peerView w).bind (fun f => f pid) = some (CurrentIdentity.identity p) := by
      rw [← peers]
      simp only [CurrentIdentity.peerView,hd,Option.map_some,Option.bind_some,hp]
    cases hw : w.dev with
    | none => simp [CurrentIdentity.peerView,hw] at old
    | some before =>
      simp only [CurrentIdentity.peerView,hw,Option.map_some,Option.bind_some] at old
      obtain ⟨q,hq,identity⟩ := Option.map_eq_some_iff.mp old
      exact ⟨before,q,rfl,hq,identity.symm⟩

end Leanux.Proofs.WG.PublicationHistory
