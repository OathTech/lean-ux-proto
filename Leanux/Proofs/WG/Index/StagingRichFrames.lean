import Leanux.Proofs.WG.Index.StagingRichEffects
import Leanux.Proofs.WG.Index.KeypairReleaseSource
import Leanux.Proofs.WG.Noise.SessionFrames
import Leanux.Proofs.WG.Index.ReleaseBounds
import Leanux.Proofs.WG.Index.PeerReleaseEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.StagingRich
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem modifyDev_rich (entry : WGWorld) (f : Device → Device)
    (cursor : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
    (peers : ∀ d, (f d).peers = d.peers)
    (keys : ∀ d, (f d).keypairs = d.keypairs) :
    Ensures (WG.modifyDev f) (Frame entry) (fun _ => Frame entry) := by
  intro g a r out b pre run
  have old := staging_modifyDev entry f cursor peers g a r out b pre.legacy run
  cases run
  refine of_same pre old ?_ ?_ ?_ ?_
  · cases hd : g.dev with
    | none => simp [table,hd]
    | some d =>
      change ((Option.map f g.dev).map Device.indexTable).getD [] = _
      simp only [table,hd,Option.map_some,Option.getD_some]
      exact congrArg Prod.fst (cursor d)
  · funext pid; simp [peerMap,Option.bind_map,Function.comp_def,peers]
  · funext kid; simp [keyMap,Option.bind_map,Function.comp_def,keys]
  · intro live d present e member kid owner
    cases hd : g.dev with
    | none => simp [hd] at present
    | some before =>
      simp only [hd,Option.map_some,Option.some.injEq] at present
      subst d
      have tab : (f before).indexTable = before.indexTable := congrArg Prod.fst (cursor before)
      obtain ⟨k,stored,pos⟩ := live before hd e (tab ▸ member) kid owner
      exact ⟨k,by simpa only [keys] using stored,pos⟩

theorem readPeer (entry : WGWorld) (pid : PeerId) {α : Type}
    (next : Peer → WG.M α) (Q : α → WGWorld → Prop)
    (body : ∀ p, peerMap entry pid = some (PeerCell p) →
      Ensures (next p) (Frame entry) Q) :
    Ensures (getPeer pid >>= next) (Frame entry) Q := by
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (getPeer_spec pid (Frame entry))) ?_
  intro p g a r f b pre run
  have observed : peerMap g pid = some (PeerCell p) := by
    change (peerAt g pid).map PeerCell = _
    rw [pre.2]
    rfl
  exact body p (pre.1.peers pid _ observed) g a r f b pre.1 run

theorem readKey (entry : WGWorld) (kid : KeypairId) {α : Type}
    (next : Keypair → WG.M α) (Q : α → WGWorld → Prop)
    (body : ∀ k, keyMap entry kid = some (KeyCell k) →
      Ensures (next k) (Frame entry) Q) :
    Ensures (getKeypair kid >>= next) (Frame entry) Q := by
  intro g a r f b pre run
  cases hd : g.dev with
  | none =>
    simp [getKeypair,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases hk : d.keypairs[kid]? with
    | none =>
      simp [getKeypair,getDev,hd,hk,invariant,AmbientM.invariant] at run
      cases run
    | some k =>
      have cell : keyMap g kid = some (KeyCell k) := by simp [keyMap,hd,hk]
      apply body k (pre.keys kid _ cell) g a r f b pre
      simpa [getKeypair,getDev,hd,hk] using run

theorem setPeer_rich (entry : WGWorld) (pid : PeerId) (p : Peer)
    (cell : peerMap entry pid = some (PeerCell p)) :
    Ensures (WG.setPeer pid p) (Frame entry) (fun _ => Frame entry) := by
  intro g a r f b pre run
  have old := staging_setPeer entry pid p (peer_legacy cell) g a r f b pre.legacy run
  cases run
  refine ⟨old,?_,?_,?_,?_⟩
  · simpa only [table,Option.map_map,Function.comp_def] using pre.tables
  · intro target c present
    cases hd : g.dev with
    | none => simp [peerMap,hd] at present
    | some d =>
      by_cases same : pid = target
      · subst target
        simp only [peerMap,hd,Option.map_some,Option.bind_some,
          Std.TreeMap.getElem?_insert_self,Option.some.injEq] at present
        subst c
        exact cell
      · apply pre.peers target c
        simpa [peerMap,hd,Std.TreeMap.getElem?_insert,same] using present
  · simpa only [keyMap,Option.bind_map,Function.comp_def] using pre.keys
  · intro live d present e member kid owner
    cases hd : g.dev with
    | none => simp [hd] at present
    | some before =>
      simp only [hd,Option.map_some,Option.some.injEq] at present
      subst d
      exact pre.live live before hd e member kid owner

theorem setKey (entry : WGWorld) (kid : KeypairId) (k : Keypair)
    (cell : keyMap entry kid = some (KeyCell k)) :
    Ensures (WG.setKeypair kid k) (Frame entry) (fun _ => Frame entry) := by
  intro g a r f b pre run
  have old := staging_modifyDev entry (fun d => {d with keypairs := d.keypairs.insert kid k})
    (fun _ => rfl) (fun _ => rfl) g a r f b pre.legacy run
  cases run
  refine ⟨old,?_,?_,?_,?_⟩
  · simpa only [table,Option.map_map,Function.comp_def] using pre.tables
  · simpa only [peerMap,Option.bind_map,Function.comp_def] using pre.peers
  · intro target c present
    cases hd : g.dev with
    | none => simp [keyMap,hd] at present
    | some d =>
      by_cases same : kid = target
      · subst target
        simp only [keyMap,hd,Option.map_some,Option.bind_some,
          Std.TreeMap.getElem?_insert_self,Option.some.injEq] at present
        subst c
        exact cell
      · apply pre.keys target c
        simpa [keyMap,hd,Std.TreeMap.getElem?_insert,same] using present
  · intro live d present e member target owner
    cases hd : g.dev with
    | none => simp [hd] at present
    | some before =>
      simp only [hd,Option.map_some,Option.some.injEq] at present
      subst d
      obtain ⟨old,stored,pos⟩ := pre.live live before hd e member target owner
      by_cases same : kid = target
      · subst target
        have cellOld : keyMap g kid = some (KeyCell old) := by simp [keyMap,hd,stored]
        have equal := Option.some.inj ((pre.keys kid _ cellOld).symm.trans cell)
        have positive := congrArg Prod.snd equal
        have positiveK : 0 < k.refcount := by
          simpa [KeyCell,pos] using positive.symm
        exact ⟨k,by simp,positiveK⟩
      · exact ⟨old,by simpa [Std.TreeMap.getElem?_insert,same] using stored,pos⟩

theorem release (entry : WGWorld) (key : Option KeypairId) (now : Bool) :
    Ensures (keypairPut key now) (Frame entry) (fun _ => Frame entry) := by
  intro g a r f b pre run
  have counter := (ensures_iff _ _ _).mpr (keypairPut_counter key now g.keypairCounter)
    g a r f b rfl run
  rcases keypairPut_normal_effect key now g f a b r run with
    ⟨_,same⟩ | ⟨id,d,k,_,device,resident,positive,actual⟩
  · exact same_device entry g f pre same counter
  · have peerFields : (releasedDevice d id k now).peers = d.peers := by
      cases now <;> by_cases last : k.refcount = 1 <;>
        simp [releasedDevice,unhashKeypair,last]
    have subset : ∀ e ∈ (releasedDevice d id k now).indexTable, e ∈ d.indexTable := by
      intro e member
      rw [released_table] at member
      split at member
      · exact (List.mem_filter.mp member).1
      · exact member
    have locals : Frame g f := by
      refine ⟨?_,?_,?_,?_,?_⟩
      · refine ⟨?_,?_,counter⟩
        · intro safe final hd
          have eq : releasedDevice d id k now = final := Option.some.inj (actual.symm.trans hd)
          subst final
          have old := safe d device
          exact ⟨released_indices d id k now old.1,released_owners d id k now old.2.1,
            released_owners_bounded d id k now old.2.2⟩
        · intro pid cell found
          simpa [stagingPeerMap,actual,device,peerFields] using found
      · simpa [table,actual,device] using subset
      · intro pid cell found
        simpa [peerMap,actual,device,peerFields] using found
      · intro kid cell found
        simp only [keyMap,actual,Option.bind_some] at found
        by_cases same : id = kid
        · subst kid
          by_cases last : k.refcount = 1
          · simp [released_keypair,last] at found
          · have reduced : 0 < k.refcount - 1 := by omega
            simp only [released_keypair,ite_eq_right last,Option.map_some,Option.some.injEq] at found
            subst cell
            simp [keyMap,device,resident,KeyCell,positive,reduced]
        · rw [released_other_keypair d id kid k now same] at found
          simpa [keyMap,device] using found
      · intro live final hd e member kid owner
        have eq : releasedDevice d id k now = final := Option.some.inj (actual.symm.trans hd)
        subst final
        obtain ⟨old,stored,pos⟩ := live d device e (subset e member) kid owner
        by_cases same : id = kid
        · subst kid
          have notLast : k.refcount ≠ 1 := by
            intro last
            exact released_unhashed d id k now (Or.inr last) e member owner
          refine ⟨{k with refcount := k.refcount - 1},?_,?_⟩
          · simpa [notLast] using released_keypair d id k now
          · change 0 < k.refcount - 1; omega
        · exact ⟨old,by rw [released_other_keypair d id kid k now same]; exact stored,pos⟩
    exact trans pre locals

theorem peerGet_rich (pid : PeerId) (entry : WGWorld) :
    Ensures (WG.peerGet pid) (Frame entry) (fun _ => Frame entry) := by
  intro g a r f b pre run
  have counter := staging_counter_snapshot _ (Keypairs.WGFrames.peerGet_sameSnapshot pid) g f a b r run
  cases device : g.dev with
  | none => simp [WG.peerGet,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none => simp [WG.peerGet,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p =>
      have effect := ((ensures_iff _ _ _).mpr (Config.peerGet_exact pid d p resident) g a r f b device run).1
      apply of_views entry g f ?_ ?_ ?_ counter pre
      · simp [effect,device,Config.withPeer,TimerDiscipline.tableCursor]
      · funext target
        simp only [peerMap,effect,device,Option.bind_some,Config.withPeer]
        exact congrFun (peerMap_write d pid p {p with refcount := p.refcount + 1} resident rfl) target
      · funext target; simp [keyMap,effect,device,Config.withPeer]

theorem keypairGet_rich (key : Option KeypairId) (entry : WGWorld) :
    Ensures (WG.keypairGet key) (Frame entry) (fun _ => Frame entry) := by
  intro g a r f b pre run
  have counter := staging_counter_snapshot _ (Keypairs.keypairGet_sameSnapshot key) g f a b r run
  cases key with
  | none =>
    simp [WG.keypairGet,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact pre
  | some id =>
    cases device : g.dev with
    | none =>
      simp [WG.keypairGet,branch,AmbientM.branch,getKeypair,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.keypairs[id]? with
      | none =>
        simp [WG.keypairGet,branch,AmbientM.branch,getKeypair,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some k =>
        have effect := Config.keypairGet_present id d k resident g a r f b device run
        by_cases zero : k.refcount = 0
        · simp only [zero,ite_true] at effect
          exact same_device entry g f pre (effect.2.trans device.symm) counter
        · simp only [zero,ite_false] at effect
          apply of_views entry g f ?_ ?_ ?_ counter pre
          · rw [effect.2,device]; rfl
          · funext target; simp [peerMap,effect.2,device,Config.withKeypair]
          · funext target
            simp only [keyMap,effect.2,device,Option.bind_some,Config.withKeypair]
            apply congrFun (keyMap_write d id k _ resident ?_) target
            simp [KeyCell,Nat.pos_of_ne_zero zero]

theorem peerPut_rich (entry : WGWorld) (peer : Option PeerId) :
    Ensures (WG.peerPut peer) (Frame entry) (fun _ => Frame entry) := by
  intro g a r f b pre run
  have old := staging_peerPut entry peer g a r f b pre.legacy run
  cases peer with
  | none =>
    simp [WG.peerPut,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact pre
  | some pid =>
    cases device : g.dev with
    | none =>
      simp [WG.peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [WG.peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0
        · simp [WG.peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,resident,zero,
            refcountDecAndTest,branchCmp,AmbientM.branchCmp,invariant,AmbientM.invariant] at run
          cases run
        · have positive : 0 < p.refcount := by omega
          have effect := peerPut_exact pid d p resident positive g a device
          change (match peerReleaseRefusal pid p with
            | some stop => Campaign2.observeResult (((WG.peerPut (some pid)).run g).run a) = .error stop
            | none => ∃ s, Campaign2.observeResult (((WG.peerPut (some pid)).run g).run a) =
              .ok ((),s) ∧ s.wg.device = some (releasedPeerDevice d pid p)) at effect
          rw [run] at effect
          cases refused : peerReleaseRefusal pid p with
          | some stop => simp [refused,Campaign2.observeResult,Except.map] at effect
          | none =>
            simp only [refused,Campaign2.observeResult,Except.map] at effect
            obtain ⟨s,equality,actual⟩ := effect
            cases equality
            change f.dev = some (releasedPeerDevice d pid p) at actual
            have subset : ∀ e ∈ (releasedPeerDevice d pid p).indexTable, e ∈ d.indexTable := by
              intro e member
              rw [releasedPeer_table] at member
              split at member
              · exact (List.mem_filter.mp member).1
              · exact member
            refine ⟨old,?_,?_,?_,?_⟩
            · intro e member
              apply pre.tables e
              simpa [table,device] using subset e (by simpa [table,actual] using member)
            · intro target cell present
              apply pre.peers target cell
              by_cases last : p.refcount = 1 <;> by_cases same : pid = target
              all_goals simp_all [peerMap,PeerCell,releasedPeerDevice,
                Std.TreeMap.getElem?_erase,Std.TreeMap.getElem?_insert]
            · intro kid cell present
              apply pre.keys kid cell
              simpa [keyMap,actual,device,releasedPeer_keypairs] using present
            · intro live final hd e member kid owner
              have eq : releasedPeerDevice d pid p = final := Option.some.inj (actual.symm.trans hd)
              subst final
              obtain ⟨k,stored,pos⟩ := pre.live live d device e (subset e member) kid owner
              exact ⟨k,by rw [releasedPeer_keypairs]; exact stored,pos⟩

theorem liftSkb_rich {α : Type} (action : SkbM α) (entry : WGWorld) :
    Ensures (liftSkb action) (Frame entry) (fun _ => Frame entry) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [liftSkb,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases executed : (action.run {txSkbs := d.txSkbs,rxSkbs := d.rxSkbs,nextSkb := d.nextSkb}).run ambient with
    | error stop =>
      simp [liftSkb,getDev,device,executed] at run
    | ok pair =>
      obtain ⟨⟨value,store⟩,inputs⟩ := pair
      simp [liftSkb,getDev,modifyDev,device,executed] at run
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      apply of_views entry g _ ?_ ?_ ?_ ?_ pre
      · rw [device]; rfl
      · funext target; simp [peerMap,device]
      · funext target; simp [keyMap,device]
      · rfl

theorem newTxSkb_rich (packet : DataPacket) (entry : WGWorld) :
    Ensures (newTxSkb packet) (Frame entry) (fun _ => Frame entry) :=
  liftSkb_rich (SkbStore.newTx packet) entry

theorem setTxSkb_rich (id : SkbId) (f : DataPacket → DataPacket) (entry : WGWorld) :
    Ensures (setTxSkb id f) (Frame entry) (fun _ => Frame entry) :=
  liftSkb_rich (SkbStore.setTx id f) entry

theorem freeTxSkb_rich (id : SkbId) (entry : WGWorld) :
    Ensures (freeTxSkb id) (Frame entry) (fun _ => Frame entry) :=
  liftSkb_rich (SkbStore.freeTx id) entry

theorem cpumaskChooseOnline_rich (pid : PeerId) (entry : WGWorld) :
    Ensures (cpumaskChooseOnline pid) (Frame entry) (fun _ => Frame entry) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [cpumaskChooseOnline,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [cpumaskChooseOnline,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      by_cases invalid : 1 ≤ p.serialWorkCpu.getD 1
      all_goals
        simp [cpumaskChooseOnline,getPeer,getDev,device,resident,invalid,branch,AmbientM.branch,
          Nat.mod_one,setPeer,modifyDev] at run
        obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      · apply of_views entry g _ ?_ ?_ ?_ ?_ pre
        · rw [device]; rfl
        · funext target
          simp only [peerMap,device,Option.bind_some]
          exact congrFun (peerMap_write d pid p {p with serialWorkCpu := some 0} resident rfl) target
        · funext target; simp [keyMap,device]
        · rfl
      · exact pre

open Lean Meta Elab Tactic in
elab "rich_getKey_bind" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Ensures do throwError "not an Ensures contract"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let binds := action.getAppArgs
  unless binds[binds.size - 2]!.consumeMData.isAppOf ``getKeypair do
    throwError "not a getKeypair bind"

end Leanux.Proofs.WG.Index.StagingRich
