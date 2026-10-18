import Leanux.Proofs.WG.Index.IncomingConsumeSource
import Leanux.Proofs.WG.Index.IncomingIndexEffects
import Leanux.Proofs.WG.Index.HashSlotLookupClaims
import Leanux.Proofs.WG.Index.RetirementRetentionClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceHeldFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do
open Queues.RxCredits

theorem modifyPeer_incomingIndexHeld (retired : Reservations)
    (pid : PeerId) (f : Peer → Peer)
    (count : ∀ p, (f p).refcount = p.refcount)
    (slots : ∀ p, clearKeys (f p) = clearKeys p)
    (stamp : ∀ p, (f p).internalId = p.internalId)
    (dead : ∀ p, (f p).isDead = p.isDead) :
    Ensures (modifyPeer pid f) (IncomingIndexHeld retired pid)
      (fun _ => IncomingIndexHeld retired pid) := by
  intro g a result out b pre run
  obtain ⟨safe,d,p,device,resident,held⟩ := pre
  change (((do let q ← getPeer pid; setPeer pid (f q)) : WG.M Unit).run g).run a = _ at run
  simp [getPeer,getDev,device,resident,setPeer,modifyDev] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  refine ⟨?_,{d with peers := d.peers.insert pid (f p)},f p,
    by simp,by simp,by rw [count]; exact held⟩
  intro final present
  simp only [Option.some.injEq] at present
  subst final
  exact incomingIndex_peerWrite retired d pid p (f p) resident
    (slots p) (stamp p) (dead p) (safe d device)

theorem peerPut_incomingIndexHeld (retired : Reservations) (pid : PeerId) :
    Ensures (peerPut (some pid)) (IncomingIndexHeld retired pid)
      (fun _ => IncomingIndexSafe retired) := by
  intro g a result out b pre run
  obtain ⟨safe,d,p,device,resident,held⟩ := pre
  have ending := peerPut_normal_device pid d p resident (by omega)
    g out a b result device run
  intro final present
  rw [ending] at present
  cases present
  exact ⟨nonlastPeerRelease_hashSlotCoverage d pid p resident (by omega) (safe d device).1,
    releasedPeer_deadHashedReserved retired d pid p resident (safe d device).2⟩

theorem pubkeyLookup_incomingIndexHeld (retired : Reservations) (key : Key) :
    Ensures (pubkeyLookup key) (IncomingIndexSafe retired)
      (fun result g => IncomingIndexSafe retired g ∧
        ∀ pid, result = some pid → IncomingIndexHeld retired pid g) := by
  intro g a result out b pre run
  have after := pubkeyLookup_preserves_acquire_source key (IncomingIndexDevice retired)
    (incomingIndex_acquire retired) g a result out b pre run
  exact ⟨after.1,fun pid returned => ⟨after.1,after.2 pid returned⟩⟩

/-- The handshake mask means even a failed lookup's actual NULL store changes
only an embedded handshake word. No key row or peer slot is reassigned. -/
theorem indexLookup_handshake_incomingIndexHeld (retired : Reservations) (index : Nat) :
    Ensures (indexLookup [.handshake] index) (IncomingIndexSafe retired)
      (fun result g => IncomingIndexSafe retired g ∧
        ∀ owner pid, result = some (owner,pid) → IncomingIndexHeld retired pid g) := by
  intro g a result out b pre run
  cases device : g.dev with
  | none =>
    rw [indexLookup_factor] at run
    simp [lookupPrefix,liftIndex,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases result with
    | none =>
      obtain ⟨final,present,cause,facts,_⟩ :=
        indexLookup_none [.handshake] index d g a none out b device run rfl
      have safe : IncomingIndexDevice retired final := by
        cases cause with
        | absentOrDisallowed =>
          obtain ⟨_,rfl⟩ := facts
          exact pre _ device
        | nullOwnerWord =>
          obtain ⟨owner,_,permitted,_,rfl⟩ := facts
          cases owner with
          | keypair kid => cases permitted
          | handshake own => exact incomingIndex_writeHandshake retired d own none (pre d device)
        | zeroReference =>
          obtain ⟨owner,pid,p,_,permitted,_,_,_,rfl⟩ := facts
          cases owner with
          | keypair kid => cases permitted
          | handshake own => exact incomingIndex_writeHandshake retired d own none (pre d device)
      refine ⟨?_,by intro owner pid impossible; cases impossible⟩
      intro actual found
      rw [present] at found
      cases found
      exact safe
    | some pair =>
      obtain ⟨owner,pid⟩ := pair
      obtain ⟨_,permitted,word,p,resident,positive,_,effect⟩ :=
        indexLookup_success [.handshake] index d g a (some (owner,pid)) out b
          device run owner pid rfl
      cases owner with
      | keypair kid => cases permitted
      | handshake own =>
        have safe : IncomingIndexSafe retired out := by
          intro actual found
          rw [effect] at found
          cases found
          exact incomingIndex_writeHandshake retired _ own (some pid)
            (incomingIndex_acquire retired d pid p resident (pre d device))
        refine ⟨safe,?_⟩
        intro other target returned
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj returned)
        refine ⟨safe,_,{p with refcount := p.refcount+1},effect,?_,by simp; omega⟩
        rw [writeOwnerWord_same_peers _ _ _
          (acquirePeer_word d pid p (.handshake own) (some pid) resident word)]
        simp [acquirePeer]
end Leanux.Proofs.WG.Index
