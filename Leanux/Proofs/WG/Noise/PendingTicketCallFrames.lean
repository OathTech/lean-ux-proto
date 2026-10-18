import Leanux.Proofs.WG.Noise.PendingTicketFrames
import Leanux.Proofs.WG.Noise.InterleavedFreshFrames
import Leanux.Proofs.WG.Noise.SessionSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes

def deviceView (counter : Nat) (d : Device) : Store PeerId :=
  ⟨counter, pending d⟩

theorem pending_some (d : Device) (pid stamp : Nat) :
    pending d pid = some stamp ↔
    ∃ p kid k, d.peers[pid]? = some p ∧ p.keypairNext = some kid ∧
      d.keypairs[kid]? = some k ∧ k.internalId = stamp := by
  simp [pending,Option.bind_eq_some_iff]

def KeyRetained (before after : Device) : Prop :=
  ∀ (kid : KeypairId) (k : Keypair), after.keypairs[kid]? = some k →
    ∃ old : Keypair, before.keypairs[kid]? = some old ∧ old.internalId = k.internalId

theorem clearPut_keys {key : Option KeypairId} {d final : Device}
    (step : ClearPut key d final) : KeyRetained d final := by
  cases step with
  | null d => exact fun kid k found => ⟨k,found,rfl⟩
  | present d kid k resident live word =>
    intro other out found
    by_cases same : kid = other
    · subst other
      rw [Index.released_keypair] at found
      split at found
      · cases found
      · cases found
        exact ⟨k,resident,rfl⟩
    · rw [Index.released_other_keypair d kid other k true same] at found
      exact ⟨out,found,rfl⟩

theorem rotation_keys {pid : PeerId} {d final : Device} {actions : List RotationAction}
    (step : RotationRun pid d actions final) : KeyRetained d final := by
  induction step with
  | nil d => exact fun kid k found => ⟨k,found,rfl⟩
  | write d final change p rest resident tail ih => exact ih
  | put d middle final key rest release tail ih =>
    intro kid k found
    obtain ⟨mid,hm,stamp⟩ := ih kid k found
    obtain ⟨old,ho,earlier⟩ := clearPut_keys release kid mid hm
    exact ⟨old,ho,earlier.trans stamp⟩

theorem rotation_pending_other {actor tracked : PeerId} {d final : Device}
    {actions : List RotationAction} (different : actor ≠ tracked)
    (steps : RotationRun actor d actions final) (stamp : Nat)
    (has : pending final tracked = some stamp) : pending d tracked = some stamp := by
  obtain ⟨p,kid,k,peer,next,key,eq⟩ := (pending_some final tracked stamp).mp has
  have beforePeer := (rotationRun_other_peer different steps).symm.trans peer
  obtain ⟨old,oldKey,stamped⟩ := rotation_keys steps kid k key
  exact (pending_some d tracked stamp).mpr
    ⟨p,kid,old,beforePeer,next,oldKey,stamped.trans eq⟩

/-- Normal confirmation consumes whichever allocation ticket is actually
resident in the entry pending slot. Missing keys carry no ticket. -/
theorem confirmation_pending_optional (pid received counter : Nat) (d final : Device)
    (p : Peer) (ok : Bool) (peer : d.peers[pid]? = some p)
    (effect : ConfirmationEffect pid received d p ok final) :
    Step (deviceView counter d) (if ok then pending d pid else none)
      (deviceView counter final) := by
  by_cases matched : p.keypairNext = some received
  · simp only [ConfirmationEffect,matched,ite_true] at effect
    obtain ⟨rfl,steps⟩ := effect
    have retained : Retained ((deviceView counter d).put pid none) (deviceView counter final) := by
      refine ⟨rfl,?_⟩
      intro tracked stamp has
      by_cases same : tracked = pid
      · subst tracked
        have afterPeer := rotationRun_peer steps p peer
        simp [deviceView,pending,afterPeer,rotationPeer,confirmationPlan,RotationWrite.apply] at has
      · have before := rotation_pending_other (Ne.symm same) steps stamp has
        simpa [Store.put,deviceView,same] using before
    cases ticket : pending d pid with
    | none =>
      simpa [ticket] using
        (Step.retained ((erase_retained (deviceView counter d) pid).trans retained))
    | some stamp =>
      exact Step.confirmed pid stamp ticket retained
  · simp only [ConfirmationEffect,matched,ite_false] at effect
    obtain ⟨rfl,rfl⟩ := effect
    exact .retained (Retained.refl _)

theorem confirmation_pending (pid received counter : Nat) (d final : Device)
    (p : Peer) (k : Keypair) (ok : Bool)
    (peer : d.peers[pid]? = some p) (key : d.keypairs[received]? = some k)
    (effect : ConfirmationEffect pid received d p ok final) :
    Step (deviceView counter d) (if ok then some k.internalId else none)
      (deviceView counter final) := by
  have step := confirmation_pending_optional pid received counter d final p ok peer effect
  cases ok with
  | false => exact step
  | true =>
    by_cases matched : p.keypairNext = some received
    · simpa [pending,peer,matched,key] using step
    · simp [ConfirmationEffect,matched] at effect

def NextBound (d : Device) : Prop :=
  ∀ (pid : PeerId) (p : Peer) (kid : KeypairId),
    d.peers[pid]? = some p → p.keypairNext = some kid → kid < d.nextKeypairId

theorem nextBound (w : WGWorld) (d : Device) (device : w.dev = some d)
    (slots : CurrentSlots.Inv w) : NextBound d := by
  intro pid p kid peer next
  exact ((CurrentSlots.inv_iff w).mp slots d pid p kid device peer
    (Or.inr (Or.inr next))).1

theorem prepared_other (pid tracked counter : Nat) (d : Device) (p : Peer) (birth : Int64)
    (different : pid ≠ tracked) (bound : NextBound d) :
    pending (sessionPrepared pid d p counter birth) tracked = pending d tracked := by
  unfold pending
  have peers : (sessionPrepared pid d p counter birth).peers[tracked]? = d.peers[tracked]? := by
    simp [sessionPrepared,sessionDerivedDevice,Index.createdDevice,
      Std.TreeMap.getElem?_insert,different]
  rw [peers]
  cases resident : d.peers[tracked]? with
  | none => rfl
  | some q =>
    cases next : q.keypairNext with
    | none => simp [next]
    | some kid =>
      have below := bound tracked q kid resident next
      simp [next,sessionPrepared,sessionDerivedDevice,Index.createdDevice,
        Std.TreeMap.getElem?_insert,Ne.symm (Nat.ne_of_lt below)]

theorem prepared_key (pid counter : Nat) (d : Device) (p : Peer) (birth : Int64)
    (k : Keypair) (found : (sessionPrepared pid d p counter birth).keypairs[d.nextKeypairId]? = some k) :
    k.internalId = counter+1 := by
  have stamp := congrArg (fun item : Option Keypair => item.map (·.internalId)) found
  by_cases role : p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE
  all_goals simpa [sessionPrepared,sessionDerivedDevice,Index.createdDevice,
    sessionAssignedKey,sessionDerivedKey,role] using stamp.symm

theorem rotation_next (p : Peer) (role : Bool) (newKey : Nat) :
    (rotationPeer (rotationPlan p role newKey) p).keypairNext =
      if role then none else some newKey := by
  cases role <;> cases next : p.keypairNext <;>
    simp [rotationPlan,rotateResponder,rotateWithNext,rotateWithoutNext,
      rotationPeer,RotationWrite.apply,next]

theorem session_pending (pid counter last : Nat) (d final : Device) (p : Peer) (ok : Bool)
    (peer : d.peers[pid]? = some p) (bound : NextBound d)
    (effect : SessionEffect pid d p counter ok final last) :
    Step (deviceView counter d) none (deviceView last final) := by
  cases ok with
  | false =>
    obtain ⟨rfl,rfl⟩ := effect
    exact .retained (Retained.refl _)
  | true =>
    obtain ⟨_,_,_,rfl,birth,rotated,steps,_,rfl⟩ := effect
    have resultPeer := rotationRun_peer steps (sessionZeroPeer p) (by simp [sessionPrepared])
    have other (tracked stamp : Nat) (different : pid ≠ tracked)
        (has : pending rotated tracked = some stamp) : pending d tracked = some stamp := by
      have old := rotation_pending_other different steps stamp has
      rw [prepared_other pid tracked counter d p birth different bound] at old
      exact old
    have actor (stamp : Nat) (has : pending rotated pid = some stamp) :
        (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) = false ∧ stamp = counter+1 := by
      obtain ⟨q,kid,k,hq,next,key,equal⟩ := (pending_some rotated pid stamp).mp has
      rw [resultPeer] at hq
      cases hq
      rw [rotation_next] at next
      cases role : p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE with
      | true => simp [role] at next
      | false =>
        simp only [role,Bool.false_eq_true,ite_false,Option.some.injEq] at next
        subst kid
        obtain ⟨old,oldKey,stampEq⟩ := rotation_keys steps d.nextKeypairId k key
        exact ⟨rfl,equal.symm.trans (stampEq.symm.trans (prepared_key pid counter d p birth old oldKey))⟩
    cases role : p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE with
    | true =>
      apply Step.unused
      refine ⟨rfl,?_⟩
      intro tracked stamp has
      change pending rotated tracked = some stamp at has
      by_cases same : pid = tracked
      · subst tracked
        have impossible := (actor stamp has).1
        rw [role] at impossible
        cases impossible
      · exact other tracked stamp same has
    | false =>
      apply Step.allocated pid
      refine ⟨rfl,?_⟩
      intro tracked stamp has
      change pending rotated tracked = some stamp at has
      by_cases same : pid = tracked
      · subst tracked
        have equal := (actor stamp has).2
        simp [Store.allocate,deviceView,equal]
      · have old := other tracked stamp same has
        simpa [Store.allocate,Store.put,deviceView,Ne.symm same] using old

end Leanux.Proofs.WG.Noise.PendingTickets

namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes

theorem beginSession_step (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p) :
    Ensures (beginSession pid)
      (fun w => w.dev = some d ∧ w.keypairCounter = counter ∧ CurrentSlots.Inv w)
      (fun _ final => Step (deviceView counter d) none (view final)) := by
  intro g ambient result final after pre run
  obtain ⟨out,device,effect⟩ :=
    beginSession_effect pid d p counter resident g ambient result final after
      ⟨pre.1,pre.2.1⟩ run
  have step := session_pending pid counter final.keypairCounter d out p result resident
    (nextBound g d pre.1 pre.2.2) effect
  simpa [view,deviceView,device] using step

theorem confirmation_counter (pid received counter : Nat) :
    Ensures (receivedWithKeypair pid received) (fun w => w.keypairCounter = counter)
      (fun _ w => w.keypairCounter = counter) := by
  let Q : WGWorld → Prop := fun w => w.keypairCounter = counter
  have read : Ensures (getPeer pid) Q (fun _ => Q) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid Q)
      g ambient p final after pre run).1
  have mark (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) Q (fun _ => Q) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) Q)
  have done (value : Bool) : Ensures (pure value : WG.M Bool) Q (fun _ => Q) := by
    intro g ambient p final after pre run
    cases run
    exact pre
  rw [receivedWithKeypair_rotation_source]
  unfold confirmationSource
  refine ensures_bind _ _ read ?_
  intro p
  refine ensures_bind _ _ (mark _ _) ?_
  intro first
  cases first with
  | true => exact done false
  | false =>
    refine ensures_bind _ _ read ?_
    intro q
    refine ensures_bind _ _ (mark _ _) ?_
    intro second
    cases second with
    | true => exact done false
    | false =>
      refine ensures_bind _ _ read ?_
      intro current
      exact ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (rotationExecute_counter pid _ counter)) (fun _ => done true)

theorem receivedWithKeypair_step (pid received counter : Nat) (d : Device)
    (p : Peer) (k : Keypair)
    (peer : d.peers[pid]? = some p) (key : d.keypairs[received]? = some k) :
    Ensures (receivedWithKeypair pid received)
      (fun w => w.dev = some d ∧ w.keypairCounter = counter)
      (fun ok final => Step (deviceView counter d)
        (if ok then some k.internalId else none) (view final)) := by
  intro g ambient ok final after pre run
  obtain ⟨out,device,effect⟩ :=
    receivedWithKeypair_effect pid received d p peer g ambient ok final after pre.1 run
  have count := confirmation_counter pid received counter g ambient ok final after pre.2 run
  have step := confirmation_pending pid received counter d out p k ok peer key effect
  simpa [view,deviceView,device,count] using step

theorem receivedWithKeypair_step_optional (pid received counter : Nat) (d : Device)
    (p : Peer) (peer : d.peers[pid]? = some p) :
    Ensures (receivedWithKeypair pid received)
      (fun w => w.dev = some d ∧ w.keypairCounter = counter)
      (fun ok final => Step (deviceView counter d)
        (if ok then pending d pid else none) (view final)) := by
  intro g ambient ok final after pre run
  obtain ⟨out,device,effect⟩ :=
    receivedWithKeypair_effect pid received d p peer g ambient ok final after pre.1 run
  have count := confirmation_counter pid received counter g ambient ok final after pre.2 run
  have step := confirmation_pending_optional pid received counter d out p ok peer effect
  simpa [view,deviceView,device,count] using step

end Leanux.Proofs.WG.Noise.PendingTickets
