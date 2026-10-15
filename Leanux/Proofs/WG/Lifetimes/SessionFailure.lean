import Leanux.Proofs.WG.Lifetimes.Session

/-! A failure after actual session allocation retains its complete observed
prefix. The hypotheses are executions of the original consecutive operations,
with no state invariant or assumptions about key-slot ownership. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- On the creation path, a missing or invalid birthdate record stops before
key derivation. The earlier peer reads, allocation, and keypair writes remain
in the history, in source order. Each premise names an original operation. -/
theorem beginSessionPrefix_clock_failure (pid : PeerId) (kp : KeypairId)
    (w allocEntry allocated guarded configured clockEntry : World)
    (h : List LifetimeEvent) (before current : Peer) (k : Keypair)
    (selected : Bool) (e : Stop)
    (hbefore : (getPeer pid).run w = .ok (before, w))
    (hstate : (sessionStateRejected before.handshakeState).run w = .ok (false, allocEntry))
    (hcreate : (keypairCreate before.handshakeEntryPeer).run allocEntry = .ok (some kp, allocated))
    (hguard : (branch .sessionNoKeypair (Option.isNone (some kp))).run allocated = .ok (false, guarded))
    (hpeer : (getPeer pid).run guarded = .ok (current, guarded))
    (hkey : (getKeypair kp).run guarded = .ok (k, guarded))
    (hwrite : (setKeypair kp {k with iAmTheInitiator := before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE, remoteIndex := current.remoteIndex}).run guarded = .ok ((), configured))
    (hselect : (branch .sessionInitiator (before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE)).run configured =
      .ok (selected, clockEntry))
    (hclock : (hiddenClock64 .deriveKeysBirthdate).run clockEntry = .error e) :
    runPrefix (beginSessionPrefix pid) w h =
      (.error e, h ++ [.peer (.read pid before.internalId), .peer (.read pid before.internalId),
        .keypair (.allocate kp (allocEntry.k.keypairCounter + 1)),
        .keypair (.write kp (allocEntry.k.keypairCounter + 1)),
        .peer (.read pid current.internalId), .keypair (.read kp k.internalId),
        .keypair (.write kp k.internalId)]) := by
  have he : allocEntry.k = w.k := sessionStateRejected_sameKernel _ w false allocEntry hstate
  have hword : (getPeer pid).run allocEntry = .ok (before, allocEntry) := by
    cases hd : w.k.wg with
    | none => simp [getPeer, getDev, getK, hd, invariant] at hbefore
    | some d =>
      cases hp : d.peers[pid]? with
      | none => simp [getPeer, getDev, getK, hd, hp, invariant] at hbefore
      | some p =>
        have hb : p = before := by simpa [getPeer, getDev, getK, hd, hp] using hbefore
        simp [getPeer, getDev, getK, he, hd, hp, hb]
  have present : guarded.k.wg.isSome = true := by
    cases hd : guarded.k.wg with
    | none => simp [getKeypair, getDev, getK, hd, invariant] at hkey
    | some d => rfl
  simp only [beginSessionPrefix, runPrefix_bind, getPeerMixed_run, hbefore,
    runPrefix_lift, hstate, Bool.false_eq_true, ↓reduceIte, peerWordPrefix,
    getPeerMixed_run, hword, runPrefix_pure,
    keypairCreatePrefix_observation, hcreate, hguard, hpeer,
    sessionKeypairPrefix, getKeypairPrefix_run, hkey, setKeypairPrefix_run,
    present, hwrite, hselect]
  cases selected <;>
    simp [runPrefix_bind, deriveKeysPrefix_clock_failure kp _ current.chainingKey clockEntry _ e hclock,
      List.append_assoc]

end Leanux.Proofs.WG.Lifetimes
