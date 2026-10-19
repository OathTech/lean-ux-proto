import Leanux.Proofs.WG.AuthenticatedEffects.ResponseLookupLoan

/-! Failed index lookups cannot clear a live resident's owner word. The
positivity premise is deliberately an actual native entry condition; its
initialized caller transport is a separate theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def Positive (w : WGWorld) : Prop :=
  ∀ pid peer, residents w pid = some peer → 0 < peer.refcount

theorem maybe_none_input (word : Option PeerId) (w v : WGWorld) (a b : Ambient)
    (positive : Positive w)
    (run : ((peerGetMaybeZero word).run w).run a = .ok ((none,v),b)) : word = none := by
  cases word with
  | none => rfl
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerGetMaybeZero,requireNotPending,getPeer,getDev,hd,invariant,AmbientM.invariant,
        branch,branch_run,StateT.run_bind] at run
      cases run
    | some device =>
      cases hp : device.peers[pid]? with
      | none =>
        simp [peerGetMaybeZero,requireNotPending,getPeer,getDev,hd,hp,invariant,AmbientM.invariant,
          branch,branch_run,StateT.run_bind] at run
        cases run
      | some peer =>
        have live : peer.refcount ≠ 0 := Nat.ne_of_gt (positive pid peer (by simp [residents,hd,hp]))
        by_cases overflow : 2147483647 ≤ peer.refcount <;>
          simp [peerGetMaybeZero,requireNotPending,getPeer,getDev,hd,hp,refcountIncNotZero,
            branch,branchCmp,branch_run,branchCmp_run,StateT.run_bind,StateT.run_pure,
            StateT.run_monadLift,except_ok_bind,except_pure,unsupported,AmbientM.unsupported,
            live,overflow,setPeer,modifyDev] at run
        all_goals cases run

def residentKeys (w : WGWorld) (kid : KeypairId) : Option Keypair :=
  w.dev.bind fun d => d.keypairs[kid]?

theorem unchanged_owner_keys (owner : IndexOwner) (word : Option PeerId)
    (w v : WGWorld) (a b : Ambient)
    (same : Affiliation.wordAt w owner = some word)
    (run : ((owner.setPeerWord word).run w).run a = .ok (((),v),b)) :
    residentKeys v = residentKeys w := by
  cases owner with
  | handshake pid =>
    unfold IndexOwner.setPeerWord at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨peer,u,c,read,write⟩ := run
    obtain ⟨rfl,rfl,device,hd,_⟩ := Queues.getPeer_normal pid w u peer a c read
    cases write
    funext kid
    simp [residentKeys,hd]
  | keypair kid =>
    obtain ⟨device,key,hd,hk,rfl,_⟩ := Origins.keypair_word_store kid word w v a b run
    have wordEq : key.peer = word := by
      simpa [Affiliation.wordAt,Affiliation.view,Affiliation.state,Affiliation.State.word,
        Affiliation.keyCell,hd,hk] using same
    funext query
    by_cases equal : kid = query
    · subst query
      simp [residentKeys,store,hd,hk,←wordEq]
    · simp [residentKeys,store,hd,Std.TreeMap.getElem?_insert,equal]

theorem acquire_none (owner : IndexOwner) (w v : WGWorld) (a b : Ambient)
    (positive : Positive w)
    (run : ((Affiliation.acquireOwner owner).run w).run a = .ok ((none,v),b)) :
    residents v = residents w ∧ residentKeys v = residentKeys w := by
  obtain ⟨word,u,q,c,d,read,borrow,write⟩ := Affiliation.acquireOwner_acquisition owner w v none a b run
  have world : u = w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerWord_preserves owner (fun z => z = w)) w a word u c rfl read
  subst u
  have wordNone := maybe_none_input word w q c d positive borrow
  subst word
  have readWord := ((hoare_iff_run_ambient _ _ _).mp
    (Affiliation.peerWord_spec owner (fun _ => True)) w a none w c True.intro read).2
  simp [peerGetMaybeZero,branch,branch_run,StateT.run_bind] at borrow
  obtain ⟨rfl,_⟩ := borrow
  exact ⟨unchanged_owner_store owner none w v d b readWord write,
    unchanged_owner_keys owner none w v d b readWord write⟩

theorem index_none (kinds : List IndexKind) (index : Nat) (w v : WGWorld) (a b : Ambient)
    (positive : Positive w)
    (run : ((indexLookup kinds index).run w).run a = .ok ((none,v),b)) :
    residents v = residents w ∧ residentKeys v = residentKeys w := by
  rw [lookup_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨⟨entry,stopped⟩,u,c,scanned,tail⟩ := run
  have same := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (scan_same_world kinds index) w a _ u c scanned
  change u = w at same
  subst u
  cases stopped <;> cases entry <;>
    simp [lookupTail,branch,StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
      except_ok_bind,except_pure] at tail
  case false.none => obtain ⟨rfl,_⟩ := tail; exact ⟨rfl,rfl⟩
  case true.none => obtain ⟨rfl,_⟩ := tail; exact ⟨rfl,rfl⟩
  case false.some entry =>
    cases acquired : ((Affiliation.acquireOwner entry.owner).run w).run
        (record (record c .idxWalk false) .idxFound true) with
    | error err => simp [acquired] at tail
    | ok out =>
      rcases out with ⟨⟨result,u⟩,d⟩
      cases result <;> simp [acquired,except_ok_bind] at tail
      rcases tail with ⟨rfl,_⟩
      exact acquire_none entry.owner w _ _ _ positive acquired
  case true.some entry =>
    cases acquired : ((Affiliation.acquireOwner entry.owner).run w).run
        (record c .idxFound true) with
    | error err => simp [acquired] at tail
    | ok out =>
      rcases out with ⟨⟨result,u⟩,d⟩
      cases result <;> simp [acquired,except_ok_bind] at tail
      rcases tail with ⟨rfl,_⟩
      exact acquire_none entry.owner w _ _ _ positive acquired

end Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
