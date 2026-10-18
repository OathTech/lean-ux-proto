import Leanux.Proofs.WG.RetirementSecurity.KeyHolderFrames
import Leanux.Proofs.WG.RetirementSecurity.WorkerHolderClosure

/-! A small physical ownership projection. Peer timer, endpoint, byte-count
and peer-reference fields are absent; key allocation stamps/counts, slot
occurrences, logical queues and packet key words remain. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

abbrev PeerOwnership := (Option KeypairId × Option KeypairId × Option KeypairId) ×
  List (List SkbId) × List SkbId

def peerOwnership (p : Peer) : PeerOwnership :=
  (slotFields p,p.txQueue.all,p.rxQueue.all)

def ownershipRows (w : WGWorld) := w.dev.map fun d =>
  d.peers.toList.map fun (pid,p) => (pid,peerOwnership p)

def ownershipView (w : WGWorld) := (keyReferenceView w,ownershipRows w,packetKeyWords w)

def rowLoans (w : WGWorld) (row : PeerId × PeerOwnership) : Option (List KeyLoan) := do
  let (pid,slots,txQueue,rxQueue) := row
  let next ← slots.1.toList.mapM (nameLoan w (.peerSlot pid .next))
  let previous ← slots.2.1.toList.mapM (nameLoan w (.peerSlot pid .previous))
  let current ← slots.2.2.toList.mapM (nameLoan w (.peerSlot pid .current))
  let tx ← txQueue.mapM (transmitLoan w pid)
  let rx ← rxQueue.mapM (receiveLoan w pid)
  return next ++ previous ++ current ++ tx ++ rx

theorem durable_rows (w : WGWorld) : durableLoans w =
    match ownershipRows w with
    | none => some []
    | some rows => (rows.mapM (rowLoans w)).map List.flatten := by
  cases device : w.dev <;>
    simp only [durableLoans,ownershipRows,device,Option.map_none,Option.map_some,List.mapM_map]
  · rfl
  · simp only [← map_eq_pure_bind]
    rfl

theorem ownership_names (same : ownershipView v = ownershipView w) :
    nameLoan v = nameLoan w ∧ transmitLoan v = transmitLoan w ∧ receiveLoan v = receiveLoan w := by
  have keys := congrArg Prod.fst same
  have names : nameLoan v = nameLoan w := by
    funext holder key
    have point := congrFun keys key
    cases hv : keyAt v key <;> cases hw : keyAt w key
    all_goals simp only [ownershipView,keyReferenceView,hv,hw,Option.map_none,Option.map_some,
      Option.some.injEq,Prod.mk.injEq,reduceCtorEq] at point
    all_goals simp_all [nameLoan]
  have tx : transmitLoan v = transmitLoan w := by
    funext pid batch
    cases head : batch.head? with
    | none => simp [transmitLoan,head]
    | some id =>
      have point := congrFun (congrArg (fun x => x.2.2.1) same) id
      cases hv : v.dev.bind (fun d => d.txSkbs[id]?) <;>
        cases hw : w.dev.bind (fun d => d.txSkbs[id]?)
      all_goals simp only [ownershipView,packetKeyWords,hv,hw,Option.map_none,Option.map_some,
        Option.some.injEq,reduceCtorEq] at point
      all_goals simp [transmitLoan,head,hv,hw,names,point]
  refine ⟨names,tx,?_⟩
  funext pid id
  have point := congrFun (congrArg (fun x => x.2.2.2) same) id
  cases hv : v.dev.bind (fun d => d.rxSkbs[id]?) <;>
    cases hw : w.dev.bind (fun d => d.rxSkbs[id]?)
  all_goals simp only [ownershipView,packetKeyWords,hv,hw,Option.map_none,Option.map_some,
    Option.some.injEq,reduceCtorEq] at point
  all_goals simp [receiveLoan,hv,hw,names,point]

theorem HolderAccount.ownership (account : HolderAccount temporary w)
    (same : ownershipView v = ownershipView w) : HolderAccount temporary v := by
  obtain ⟨loans,projected,credits⟩ := account
  obtain ⟨names,tx,rx⟩ := ownership_names same
  have rows : ownershipRows v = ownershipRows w := congrArg (fun x => x.2.1) same
  have functions : rowLoans v = rowLoans w := by funext row; simp only [rowLoans,names,tx,rx]
  refine ⟨loans,?_,credits.reference_view (congrArg Prod.fst same)⟩
  simpa only [durable_rows,rows,functions] using projected

theorem ownership_preserves (action : WG.M α) (same : SameView ownershipView action)
    (temporary : Credits.Ledger) : Preserves (HolderAccount temporary) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  exact account.ownership ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem ownership_rows_replace (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (fields : peerOwnership q = peerOwnership p) :
    ownershipRows (replacePeer w d pid q) = ownershipRows w := by
  have maps : ((d.peers.insert pid q).map (fun _ => peerOwnership)).Equiv
      (d.peers.map (fun _ => peerOwnership)) := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro other
    by_cases same : pid = other
    · subst other
      simp [Std.TreeMap.getElem?_map,found,fields]
    · simp [Std.TreeMap.getElem?_map,Std.TreeMap.getElem?_insert,same]
  have rows := maps.toList_eq
  simpa only [ownershipRows,replacePeer,device,Option.map_some,Std.TreeMap.toList_map] using
    congrArg some rows

theorem ownership_replace (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (fields : peerOwnership q = peerOwnership p) :
    ownershipView (replacePeer w d pid q) = ownershipView w := by
  apply Prod.ext
  · change keyReferenceView (replacePeer w d pid q) = keyReferenceView w
    funext id
    simp [keyReferenceView,keyAt,replacePeer,device]
  · exact Prod.ext (ownership_rows_replace device found fields)
      (by simp [ownershipView,packetKeyWords,replacePeer,device])

theorem updatePeer_ownership (pid : PeerId) (f : Peer → Peer)
    (fields : ∀ p, peerOwnership (f p) = peerOwnership p) :
    SameView ownershipView (updatePeer pid f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  rw [updatePeer,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,setRun⟩ := run
  obtain ⟨same,ambient,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have after : replacePeer w d pid (f p) = v ∧ a = b := by
    simpa [setPeer,modifyDev,replacePeer,device] using setRun
  rw [← after.1]
  exact ownership_replace device stored (fields p)

def ownershipAt (w : WGWorld) (pid : PeerId) := (peerAt w pid).map peerOwnership

def ownershipPointView (w : WGWorld) :=
  (keyReferenceView w,w.dev.isSome,(fun pid => ownershipAt w pid),packetKeyWords w)

theorem ownership_of_points (same : ownershipPointView v = ownershipPointView w) :
    ownershipView v = ownershipView w := by
  have present := congrArg (fun x => x.2.1) same
  have cells := congrArg (fun x => x.2.2.1) same
  have rows : ownershipRows v = ownershipRows w := by
    cases dv : v.dev <;> cases dw : w.dev
    all_goals simp only [ownershipPointView,dv,dw,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,Bool.true_eq_false] at present
    all_goals try contradiction
    · simp [ownershipRows,dv,dw]
    · rename_i vd wd
      have maps : (vd.peers.map (fun _ => peerOwnership)).Equiv
          (wd.peers.map (fun _ => peerOwnership)) := by
        apply Std.TreeMap.Equiv.of_forall_constGet?_eq
        intro pid
        simpa only [ownershipPointView,ownershipAt,peerAt,dv,dw,Option.bind_some,
          Std.TreeMap.getElem?_map] using congrFun cells pid
      simpa only [ownershipRows,dv,dw,Option.map_some,Std.TreeMap.toList_map] using
        congrArg some maps.toList_eq
  have keys : keyReferenceView v = keyReferenceView w := congrArg (fun x => x.1) same
  have packets : packetKeyWords v = packetKeyWords w := congrArg (fun x => x.2.2.2) same
  exact Prod.ext keys (Prod.ext rows packets)

theorem HolderAccount.points (account : HolderAccount temporary w)
    (same : ownershipPointView v = ownershipPointView w) : HolderAccount temporary v :=
  account.ownership (ownership_of_points same)

theorem ownershipPoints_kernel (action : WG.M α) (same : SameWGStore action) :
    SameView ownershipPointView action :=
  same.of_factor (fun store : WGStoreView =>
    ((fun id => (store.dev.bind fun d => d.keypairs[id]?).map fun k => (k.internalId,k.refcount)),
     store.dev.isSome,(fun pid => (store.dev.bind fun d => d.peers[pid]?).map peerOwnership),
     (fun id => (store.dev.bind fun d => d.txSkbs[id]?).map (·.keypair)),
     (fun id => (store.dev.bind fun d => d.rxSkbs[id]?).map (·.keypair))))
    ownershipPointView (fun _ => rfl)

theorem ownership_getPeer (P : _ → Prop) (pid : PeerId) :
    Hoare (getPeer pid) (fun w => P (ownershipPointView w))
      (fun p w => P (ownershipPointView w) ∧ ownershipAt w pid = some (peerOwnership p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b before run
  obtain ⟨world,ambient,d,device,stored⟩ := Origins.getPeer_return pid w v p a b run
  subst v
  exact ⟨before,by simp [ownershipAt,peerAt,device,stored]⟩

theorem ownership_setPeer (P : _ → Prop) (pid : PeerId) (p : Peer) :
    Hoare (setPeer pid p)
      (fun w => P (ownershipPointView w) ∧ ownershipAt w pid = some (peerOwnership p))
      (fun _ w => P (ownershipPointView w)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases device : w.dev with
  | none => simp [ownershipAt,peerAt,device] at before
  | some d =>
    obtain ⟨old,found,fields⟩ := Option.map_eq_some_iff.mp
      (by simpa only [ownershipAt,peerAt,device,Option.bind_some] using before.2)
    cases run
    have same : ownershipPointView (replacePeer w d pid p) = ownershipPointView w := by
      unfold ownershipPointView keyReferenceView
      dsimp only [keyAt,ownershipAt,peerAt,packetKeyWords]
      simp only [replacePeer,device,Option.bind_some,Option.isSome_some,Prod.mk.injEq,
        true_and,and_true]
      funext other
      by_cases eq : pid = other
      · subst other; simp [found,fields]
      · simp [Std.TreeMap.getElem?_insert,eq]
    simpa only [replacePeer,device,Option.map_some] using same.symm ▸ before.1

theorem ownership_modifyDev (f : Device → Device)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (peers : ∀ d, (f d).peers = d.peers)
    (tx : ∀ d, (f d).txSkbs = d.txSkbs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs) :
    SameView ownershipPointView (modifyDev f) := by
  intro initial
  apply hoare_modify
  intro w before
  unfold ownershipPointView keyReferenceView at before ⊢
  dsimp only [keyAt,ownershipAt,peerAt,packetKeyWords] at before ⊢
  simpa only [Option.map_map,Option.bind_map,Function.comp_def,keys,peers,tx,rx,
    Option.isSome_map] using before

end Leanux.Proofs.WG.RetirementSecurity
