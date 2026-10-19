import Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness

/-! Native acquisition/payment and clear frames for slot liveness. Reference
counts and nullable owner words may change; deleting a peer removes obligations
only for that resident. Pending removal exceptions remain explicit. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem device (before : InvExcept pending w) (same : v.dev=w.dev) : InvExcept pending v :=
  peers before (by simp only [peersAt,same])

theorem peer_get_maybe (word : Option PeerId) : Preserves (InvExcept pending) (peerGetMaybeZero word) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := ((hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec word (wgStoreView w)) w a result v b rfl run).2
  cases result with
  | none => exact device before (congrArg WGStoreView.dev borrowed)
  | some pid =>
    obtain ⟨d,p,hd,hp,_,out⟩ := borrowed
    exact device (replace before hd hp (q:={p with refcount:=p.refcount+1}) (fun h=>h) (fun h=>h))
      (congrArg WGStoreView.dev out)

theorem peer_get (pid : PeerId) : Preserves (InvExcept pending) (peerGet pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  obtain ⟨d,p,hd,hp,_,out⟩ := peerGet_loan pid w v a b run
  exact device (replace before hd hp (q:={p with refcount:=p.refcount+1}) (fun h=>h) (fun h=>h))
    (congrArg WGStoreView.dev out)

theorem get_key (id : KeypairId) : Preserves (InvExcept pending) (getKeypair id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (KeyTimes.getKeypair_return id w v result a b run).1 ▸ before

theorem set_key (id : KeypairId) (key : Keypair) : Preserves (InvExcept pending) (setKeypair id key) :=
  modify _ (fun _=>rfl)

theorem set_word (owner : IndexOwner) (word : Option PeerId) :
    Preserves (InvExcept pending) (owner.setPeerWord word) := by
  cases owner with
  | handshake pid => exact update pid (fun p=>{p with handshakeEntryPeer:=word}) (fun _ h=>h) (fun _ h=>h)
  | keypair id =>
    unfold IndexOwner.setPeerWord
    exact preserves_bind (get_key id) (fun k=>set_key id {k with peer:=word})

theorem acquire (owner : IndexOwner) : Preserves (InvExcept pending) (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  apply preserves_bind (indexOwner_peerWord_preserves _ _)
  intro word
  apply preserves_bind (peer_get_maybe word)
  intro acquired
  exact preserves_bind (set_word owner acquired) (fun _=>preserves_pure acquired)

theorem lookup (kinds : List IndexKind) (number : Nat) : Preserves (InvExcept pending) (indexLookup kinds number) := by
  rw [←Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head Affiliation.acquireOwner; exact acquire _)
    | (allocation_release_lift_from IndexM; exact index _)
    | (rx_retention_head liftIndex; exact index _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (InvExcept pending)
       intro x u
       change Preserves (InvExcept pending) _)
    | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rxstack_preserves_join
    | rx_retention_step

theorem pubkey (key : Key) : Preserves (InvExcept pending) (pubkeyLookup key) := by
  unfold pubkeyLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact peer_get_maybe _)
    | (rx_retention_head getDev; exact store getDev_sameWGStore)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem peer_put (word : Option PeerId) : Preserves (InvExcept pending) (peerPut word) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  cases word with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact before
  | some pid =>
    cases device : w.dev with
    | none =>
      simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,
        invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases stored : d.peers[pid]? with
      | none =>
        simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,stored,
          invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        have lift (action : IndexM Unit) : (liftM action : WG.M Unit)=liftIndex action := rfl
        by_cases positive : 0<p.refcount
        · have nonzero : p.refcount≠0 := by omega
          by_cases final : p.refcount=1
          all_goals simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,lift,liftIndex_run,
            retirePeerUnits,modifyAmbient,CounterWindow.branch_run,CounterWindow.branchCmp_run,
            device,stored,positive,nonzero,final,StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
            CounterWindow.except_ok_bind,CounterWindow.except_pure,invariant,AmbientM.invariant,
            unsupported,AmbientM.unsupported] at run
          all_goals repeat' first | split at run | contradiction
          all_goals rcases run with ⟨rfl,rfl⟩
          all_goals intro other current found outside slots
          all_goals by_cases same : pid=other
          all_goals simp [peerAt,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase,same] at found
          all_goals first
            | (subst other; subst current; exact before pid p (by simp [peerAt,device,stored]) outside slots)
            | exact before other current (by simpa [peerAt,device] using found) outside slots
        · have zero : p.refcount=0 := by omega
          simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,refcountDecAndTest,
            branch,branchCmp,CounterWindow.branch_run,CounterWindow.branchCmp_run,device,stored,zero,
            StateT.run_bind,StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind,
            CounterWindow.except_pure,unsupported,AmbientM.unsupported] at run
          cases run

/-- A saved read carries its own dead/slot relation across callbacks. The
later cached setter must prove that relation for the actual record it writes. -/
theorem read (pid : PeerId) : Hoare (getPeer pid) (InvExcept pending)
    (fun p w=>InvExcept pending w ∧ (pid∉pending → HasKeySlot p → p.isDead=false)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b before run
  obtain ⟨same,_,d,device,stored⟩ := getPeer_normal pid w v p a b run
  subst v
  exact ⟨before,before pid p (by simp [peerAt,device,stored])⟩

theorem read_bind (pid : PeerId) (tail : Peer → WG.M α)
    (next : ∀p,(pid∉pending → HasKeySlot p → p.isDead=false) →
      Preserves (InvExcept pending) (tail p)) :
    Preserves (InvExcept pending) (getPeer pid >>= tail) := by
  apply hoare_bind _ _ (read pid)
  intro p
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (hoare_iff_run_ambient _ _ _).mp (next p before.2) w a result v b before.1 run

theorem set_saved (pid : PeerId) (p : Peer)
    (saved : pid∉pending → HasKeySlot p → p.isDead=false) :
    Preserves (InvExcept pending) (setPeer pid p) := by
  unfold setPeer modifyDev
  apply hoare_modify
  intro w before other q found outside slots
  cases device : w.dev with
  | none => simp [peerAt,device] at found
  | some d =>
    by_cases same : pid=other
    · subst other
      simp [peerAt,device] at found
      subst q
      exact saved outside slots
    · exact before other q (by simpa [peerAt,device,Std.TreeMap.getElem?_insert,same] using found) outside slots

macro "key_slot_saved_step" : tactic => `(tactic| first
  | (env_bind_head getPeer; apply read_bind; intro p saved)
  | (rx_retention_head setPeer; apply set_saved; assumption))

macro "key_slot_step" : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply update
     · intro p h; exact h
     · intro p h; exact h)
  | (receive_update_head Bind.bind
     apply update_then
     · intro p h; exact h
     · intro p h; exact h
     intro x)
  | (rx_retention_head peerPut; exact peer_put _)
  | (rx_retention_head peerGet; exact peer_get _)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head getKeypair; exact get_key _)
  | (rx_retention_head setKeypair; exact set_key _ _)
  | (rx_retention_head keypairPut; exact key_put _ _)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rxstack_preserves_join
  | rx_retention_step)

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
