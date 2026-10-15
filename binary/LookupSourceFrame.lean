import MirrorPeerPoints
import OwnerStore

namespace Binary.LookupSourceFrame
open Leanux Leanux.WG MirrorHistory

/-- Lifetime stamp, keypair existence and every replay bitmap word. The
    embedded peer word is intentionally absent: lookup may clear it. -/
def receivingSnapshot (w : World) : Nat × (KeypairId → Option (Nat × ReplayCounter)) :=
  (w.k.keypairCounter, fun i => (w.k.wg.bind fun d => d.keypairs.get? i).map
    fun k => (k.internalId, k.receivingCounter))

def Preserves (project : World → σ) (a : M α) : Prop :=
  ∀ w x w', a.run w = .ok (x,w') → project w' = project w

def Frames (project : World → σ) (a : Logged α) : Prop :=
  ∀ initial history w x points w', project w = initial →
    (∀ p ∈ history, project p.world = initial) →
    (a.run history).run w = .ok ((x,points),w') →
    project w' = initial ∧ ∀ p ∈ points, project p.world = initial

theorem frames_pure (project : World → σ) (x : α) : Frames project (pure x) := by
  intro initial history w y points w' same prior run
  cases run
  exact ⟨same,prior⟩

theorem frames_bind {project : World → σ} {a : Logged α} {f : α → Logged β}
    (ha : Frames project a) (hf : ∀ x, Frames project (f x)) : Frames project (a >>= f) := by
  intro initial history w y points w' same prior run
  cases first : (a.run history).run w with
  | error e =>
    simp only [StateT.run_bind, first] at run
    change Except.error e = Except.ok ((y,points),w') at run
    contradiction
  | ok out =>
    obtain ⟨⟨x,middle⟩,intermediate⟩ := out
    simp only [StateT.run_bind, first] at run
    have kept := ha initial history w x middle intermediate same prior first
    exact hf x initial middle intermediate y points w' kept.1 kept.2 run

theorem frames_lift {project : World → σ} {a : M α} (ha : Preserves project a) :
    Frames project (StateT.lift a) := by
  intro initial history w x points w' same prior run
  cases actual : a.run w with
  | error e =>
    simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, actual] at run
    change Except.error e = Except.ok ((x,points),w') at run
    contradiction
  | ok out =>
    obtain ⟨value,after⟩ := out
    simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, actual] at run
    change Except.ok ((value,history),after) = Except.ok ((x,points),w') at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := Prod.mk.inj (Except.ok.inj run.symm)
    exact ⟨(ha w x w' actual).trans same,prior⟩

theorem frames_mark (project : World → σ) (tag : Tag) : Frames project (mark tag) := by
  intro initial history w x points w' same prior run
  rw [mark_run] at run
  cases run
  refine ⟨same,?_⟩
  intro p member
  rcases List.mem_append.mp member with old | added
  · exact prior p old
  · have eq := List.mem_singleton.mp added
    subst p
    exact same

theorem frames_called {project : World → σ} (symbol : String) {a : Logged α}
    (ha : Frames project a) : Frames project (called symbol a) := by
  unfold called
  apply frames_bind (frames_mark project _)
  intro _
  apply frames_bind ha
  intro answer
  apply frames_bind (frames_mark project _)
  intro _
  exact frames_pure project answer

theorem frames_forIn {project : World → σ} (xs : List α) (b : β)
    (body : α → β → Logged (ForInStep β))
    (hb : ∀ x b, Frames project (body x b)) : Frames project (forIn xs b body) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using frames_pure project b
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply frames_bind (hb x b)
    intro step
    cases step with
    | done value => exact frames_pure project value
    | yield value => exact ih value


theorem preserves_pure (project : World → σ) (x : α) : Preserves project (pure x) := by
  intro w y w' run
  cases run
  rfl

theorem preserves_get (project : World → σ) : Preserves project (get : M World) := by
  intro w x w' run
  cases run
  rfl

theorem preserves_throw (project : World → σ) (e : Stop) :
    Preserves project (throw e : M α) := by
  intro w x w' run
  cases run

theorem preserves_bind {project : World → σ} {a : M α} {f : α → M β}
    (ha : Preserves project a) (hf : ∀ x, Preserves project (f x)) :
    Preserves project (a >>= f) := by
  intro w y w' run
  simp only [StateT.run_bind] at run
  cases actual : a.run w with
  | error e =>
    simp only [actual] at run
    change Except.error e = Except.ok (y,w') at run
    contradiction
  | ok out =>
    obtain ⟨x,middle⟩ := out
    simp only [actual] at run
    exact (hf x middle y w' run).trans (ha w x middle actual)

theorem preserves_getDev (project : World → σ) : Preserves project getDev := by
  unfold getDev getK
  apply preserves_bind (preserves_bind (preserves_get project) (fun _ => preserves_pure project _))
  intro k
  cases k.wg with
  | none => exact preserves_throw project _
  | some d => exact preserves_pure project d

theorem preserves_getPeer (project : World → σ) (id : PeerId) : Preserves project (getPeer id) := by
  unfold getPeer
  apply preserves_bind (preserves_getDev project)
  intro d
  cases d.peers.get? id with
  | none => exact preserves_throw project _
  | some p => exact preserves_pure project p

theorem preserves_getKeypair (project : World → σ) (id : KeypairId) : Preserves project (getKeypair id) := by
  unfold getKeypair
  apply preserves_bind (preserves_getDev project)
  intro d
  cases d.keypairs.get? id with
  | none => exact preserves_throw project _
  | some p => exact preserves_pure project p

theorem preserves_setPeer (id : PeerId) (p : Peer) :
    Preserves receivingSnapshot (setPeer id p) := by
  intro w x w' run
  cases run
  cases h : w.k.wg <;> simp [receivingSnapshot, h]

theorem preserves_ownerWord (owner : IndexOwner) :
    Preserves receivingSnapshot owner.peerWord := by
  cases owner with
  | handshake id =>
    exact preserves_bind (preserves_getPeer receivingSnapshot id) (fun _ => preserves_pure receivingSnapshot _)
  | keypair id =>
    exact preserves_bind (preserves_getKeypair receivingSnapshot id) (fun _ => preserves_pure receivingSnapshot _)

theorem preserves_ownerStore (owner : IndexOwner) (word : Option PeerId) :
    Preserves receivingSnapshot (owner.setPeerWord word) := by
  intro w x w' run
  cases hd : w.k.wg with
  | none =>
    cases owner <;> simp [IndexOwner.setPeerWord, getPeer, getKeypair, getDev, getK, hd, invariant] at run <;> cases run
  | some d =>
    cases owner with
    | handshake id =>
      cases hp : d.peers.get? id with
      | none =>
        have missing : d.peers[id]? = none := hp
        simp [IndexOwner.setPeerWord, getPeer, getDev, getK, hd, missing, invariant] at run
        cases run
      | some p =>
        rw [OwnerWord.set_handshake_run w d id p word hd hp] at run
        cases run
        simp [receivingSnapshot, hd]
    | keypair id =>
      cases hk : d.keypairs.get? id with
      | none =>
        have missing : d.keypairs[id]? = none := hk
        simp [IndexOwner.setPeerWord, getKeypair, getDev, getK, hd, missing, invariant] at run
        cases run
      | some kp =>
        rw [OwnerWord.set_keypair_run w d id kp word hd hk] at run
        cases run
        unfold receivingSnapshot
        apply Prod.ext
        · rfl
        · funext other
          by_cases same : id = other
          · subst other
            have found : d.keypairs[id]? = some kp := hk
            simp [hd, found]
          · simp [hd, Std.TreeMap.getElem?_insert, same]


theorem frames_branch (d : Decision) (b : Bool) :
    Frames receivingSnapshot (branchLogged d b) := by
  unfold branchLogged
  apply frames_bind (frames_lift (show Preserves receivingSnapshot (branch d b) from by
    intro w x w' run
    cases run
    rfl))
  intro answer
  apply frames_bind (frames_mark receivingSnapshot _)
  intro _
  exact frames_pure receivingSnapshot answer

theorem frames_count (old : Nat) : Frames receivingSnapshot (count old) := by
  intro initial history w answer points w' same prior run
  have erased := count_erases old history w
  rw [run] at erased
  have actual : (refcountIncNotZero old).run w = .ok (answer,w') := erased.symm
  have small := PeerMirror.accepted_count_bound old w w' answer actual
  rw [count_run_logged old history w small] at run
  cases run
  have kernel : (PeerMirror.countRecords w old).k = w.k := by
    unfold PeerMirror.countRecords
    split <;> rfl
  refine ⟨?_,?_⟩
  · simpa only [receivingSnapshot, kernel] using same
  · intro p member
    rcases List.mem_append.mp member with original | added
    · exact prior p original
    · have kernel := countPoints_kernel w old p added
      simpa only [receivingSnapshot, kernel] using same

theorem frames_peerGet (peer : Option PeerId) : Frames receivingSnapshot (peerGet peer) := by
  unfold MirrorHistory.peerGet
  apply frames_bind (frames_branch _ _)
  intro null
  cases null with
  | true => exact frames_pure receivingSnapshot _
  | false =>
    cases peer with
    | none => exact frames_lift (preserves_throw receivingSnapshot _)
    | some pid =>
      apply frames_bind (frames_lift (preserves_pure receivingSnapshot ()))
      intro _
      apply frames_bind (frames_lift (preserves_getPeer receivingSnapshot pid))
      intro p
      apply frames_bind (frames_count p.refcount)
      intro live
      apply frames_bind (frames_branch _ _)
      intro dead
      cases dead with
      | true => exact frames_pure receivingSnapshot _
      | false =>
        apply frames_bind (frames_lift (preserves_setPeer pid _))
        intro _
        exact frames_pure receivingSnapshot _

theorem frames_body (kinds : List IndexKind) (index : Nat)
    (e : IndexEntry) (a : LookupMirror.Acc) : Frames receivingSnapshot (body kinds index e a) := by
  unfold body
  apply frames_bind (frames_branch _ _)
  intro _
  apply frames_bind (frames_branch _ _)
  intro hit
  cases hit with
  | false => exact frames_pure receivingSnapshot _
  | true =>
    apply frames_bind (frames_branch _ _)
    intro good
    exact frames_pure receivingSnapshot _

theorem frames_finish (a : LookupMirror.Acc) : Frames receivingSnapshot (finish a) := by
  unfold finish
  cases stop : a.2 <;> simp only [stop, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  all_goals try (apply frames_bind (frames_branch .idxWalk false); intro _)
  all_goals
    apply frames_bind (frames_branch _ _)
    intro found
    cases found with
    | false => exact frames_pure receivingSnapshot _
    | true =>
      cases h : a.1 with
      | none =>
        apply frames_bind (frames_lift (preserves_throw receivingSnapshot _))
        intro _
        exact frames_pure receivingSnapshot _
      | some e =>
        apply frames_bind (frames_lift (preserves_ownerWord e.owner))
        intro word
        apply frames_bind (frames_called "wg_peer_get_maybe_zero" (frames_peerGet word))
        intro peer
        apply frames_bind (frames_lift (preserves_ownerStore e.owner peer))
        intro _
        apply frames_bind (frames_branch _ _)
        intro alive
        cases alive with
        | false => exact frames_pure receivingSnapshot _
        | true =>
          cases peer with
          | none =>
            apply frames_bind (frames_lift (preserves_throw receivingSnapshot _))
            intro _
            exact frames_pure receivingSnapshot _
          | some pid => exact frames_pure receivingSnapshot _

theorem frames_lookup (kinds : List IndexKind) (index : Nat) :
    Frames receivingSnapshot (lookup kinds index) := by
  unfold lookup
  apply frames_called
  apply frames_bind (frames_lift (show Preserves receivingSnapshot (indexBucket index) from by
    unfold indexBucket
    apply preserves_bind (preserves_getDev receivingSnapshot)
    intro d
    exact preserves_pure receivingSnapshot _))
  intro es
  apply frames_bind (frames_forIn es (none,false) (body kinds index) (frames_body kinds index))
  exact frames_finish

theorem lookup_receivingSnapshot (kinds : List IndexKind) (index : Nat)
    (world final : World) (answer : Option (IndexOwner × PeerId)) (points : List Point)
    (accepted : ((lookup kinds index).run []).run world = .ok ((answer,points),final)) :
    receivingSnapshot final = receivingSnapshot world ∧
      ∀ point ∈ points, receivingSnapshot point.world = receivingSnapshot world :=
  frames_lookup kinds index (receivingSnapshot world) [] world answer points final rfl
    (by intro p member; cases member) accepted

#print axioms lookup_receivingSnapshot
end Binary.LookupSourceFrame
