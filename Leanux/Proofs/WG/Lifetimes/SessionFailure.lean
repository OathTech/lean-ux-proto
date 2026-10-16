import Leanux.Proofs.WG.Lifetimes.Session

/-! A failure after actual session allocation retains its complete observed
prefix. The hypotheses are executions of the original consecutive operations,
with no state invariant or assumptions about key-slot ownership. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

/-- On the creation path, a missing or invalid birthdate record stops before
key derivation. The earlier peer reads, allocation, and keypair writes remain
in the history, in source order. Each premise names an original operation. -/
theorem beginSessionPrefix_clock_failure (pid : PeerId) (kp : KeypairId)
    (w allocEntry allocated guarded configured clockEntry : WGWorld)
    (ambient allocAmbient allocatedAmbient guardedAmbient configuredAmbient clockAmbient : Ambient)
    (h : List LifetimeEvent) (before current : Peer) (k : Keypair)
    (selected : Bool) (e : Stop)
    (hbefore : ((getPeer pid).run w).run ambient = .ok ((before, w), ambient))
    (hstate : ((MonadLift.monadLift (sessionStateRejected before.handshakeState) : WG.M Bool).run w).run ambient =
      .ok ((false, allocEntry), allocAmbient))
    (hcreate : ((keypairCreate before.handshakeEntryPeer).run allocEntry).run allocAmbient =
      .ok ((some kp, allocated), allocatedAmbient))
    (hguard : ((branch .sessionNoKeypair (Option.isNone (some kp)) : WG.M Bool).run allocated).run allocatedAmbient =
      .ok ((false, guarded), guardedAmbient))
    (hpeer : ((getPeer pid).run guarded).run guardedAmbient = .ok ((current, guarded), guardedAmbient))
    (hkey : ((getKeypair kp).run guarded).run guardedAmbient = .ok ((k, guarded), guardedAmbient))
    (hwrite : ((setKeypair kp {k with iAmTheInitiator := before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE, remoteIndex := current.remoteIndex}).run guarded).run guardedAmbient = .ok (((), configured), configuredAmbient))
    (hselect : ((branch .sessionInitiator (before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) : WG.M Bool).run configured).run configuredAmbient =
      .ok ((selected, clockEntry), clockAmbient))
    (hclock : ((hiddenClock64 .deriveKeysBirthdate : WG.M Int64).run clockEntry).run clockAmbient = .error e) :
    runStatePrefix (beginSessionPrefix pid) w ambient h =
      (.error e, h ++ [.peer (.read pid before.internalId), .peer (.read pid before.internalId),
        .keypair (.allocate kp (allocEntry.keypairCounter + 1)),
        .keypair (.write kp (allocEntry.keypairCounter + 1)),
        .peer (.read pid current.internalId), .keypair (.read kp k.internalId),
        .keypair (.write kp k.internalId)]) := by
  have he : allocEntry = w :=
    (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (sessionStateRejected before.handshakeState) (fun g => g = w))
      w ambient false allocEntry allocAmbient rfl hstate
  have hword : ((getPeer pid).run allocEntry).run allocAmbient =
      .ok ((before, allocEntry), allocAmbient) := by
    cases hd : w.dev with
    | none =>
      simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hbefore
      cases hbefore
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hbefore
        cases hbefore
      | some p =>
        have hb : p = before := by simpa [getPeer, getDev, hd, hp] using hbefore
        simp [getPeer, getDev, he, hd, hp, hb] <;> rfl
  have present : guarded.dev.isSome = true := by
    cases hd : guarded.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hkey
      cases hkey
    | some d => rfl
  simp only [beginSessionPrefix, liftWGPrefix, runStatePrefix_bind, getPeerMixed_run, hbefore,
    runStatePrefix_lift, hstate, Bool.false_eq_true, ↓reduceIte, peerWordPrefix,
    getPeerMixed_run, hword, runStatePrefix_pure,
    keypairCreatePrefix_observation, hcreate, hguard, hpeer,
    sessionKeypairPrefix, getKeypairPrefix_run, hkey, setKeypairPrefix_run,
    present, hwrite, hselect]
  cases selected <;>
    simp [runStatePrefix_bind, deriveKeysPrefix_clock_failure kp _ current.chainingKey
      clockEntry clockAmbient _ e hclock, List.append_assoc]

end Leanux.Proofs.WG.Lifetimes
