import Leanux.Proofs.WG.Noise.SessionTagFrames
import Leanux.Proofs.WG.Noise.SessionSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Whole session normal-return effect, with residency derived from its actual
first read. No allocation freshness or release budget is assumed. -/
theorem beginSession_tagMap (pid : PeerId) (entry : Option Device) :
    Ensures (beginSession pid) (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun ok g => (∀target, responseTagMap g.dev target =
        if ok then if pid = target then some HANDSHAKE_ZEROED else responseTagMap entry target
        else responseTagMap entry target) ∧
        (ok = true → responseTagMap entry pid = some HANDSHAKE_CREATED_RESPONSE ∨
          responseTagMap entry pid = some HANDSHAKE_CONSUMED_RESPONSE)) := by
  intro g ambient ok out after pre run
  cases device : g.dev with
  | none =>
    simp [beginSession,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [beginSession,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨final,finalDevice,effect⟩ := beginSession_effect pid d p g.keypairCounter resident
        g ambient ok out after ⟨device,rfl⟩ run
      have original : responseTagMap (some d) = responseTagMap entry := by simpa [device] using pre
      cases ok with
      | false =>
        obtain ⟨rfl,_⟩ := effect
        refine ⟨?_,by simp⟩
        intro target
        simpa [finalDevice] using congrFun original target
      | true =>
        obtain ⟨accepted,_,_,_,birth,rotated,steps,_,rfl⟩ := effect
        have preserved := rotationRun_tagMap steps
        refine ⟨?_,?_⟩
        · intro target
          change responseTagMap out.dev target = _
          rw [finalDevice]
          change responseTagMap (some rotated) target = _
          rw [preserved]
          by_cases same : pid = target
          · subst target
            simp [sessionPrepared,sessionDerivedDevice,Index.createdDevice,sessionZeroPeer,
              responseTagMap,HANDSHAKE_ZEROED]
          · have old := congrFun original target
            simpa [sessionPrepared,sessionDerivedDevice,Index.createdDevice,sessionZeroPeer,
              responseTagMap,Std.TreeMap.getElem?_insert,same] using old
        · intro _
          have old : responseTagMap entry pid = some p.handshakeState := by
            rw [← original]
            simp [responseTagMap,resident]
          cases accepted with
          | inl eq => exact Or.inl (old.trans (congrArg some eq))
          | inr eq => exact Or.inr (old.trans (congrArg some eq))

/-- Normal handshake clearing zeroes just the requested tag. NULL words and
missing peers retain the original stopped paths, without extra entry premises. -/
theorem handshakeClear_tagMap (pid : PeerId) (entry : Option Device) :
    Ensures (handshakeClear pid) (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => ∀target, responseTagMap g.dev target =
        if pid = target then some HANDSHAKE_ZEROED else responseTagMap entry target) := by
  intro g ambient result out after pre run
  cases device : g.dev with
  | none =>
    simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have exactClear : Ensures (handshakeClear pid) (fun g => g.dev = some d)
          (fun _ g => g.dev = some (Config.expiryZeroDevice d pid p)) := by
        simpa only [Config.expiryReadPrefix,requireNotPending,pure_bind] using
          Config.expiryReadPrefix_exact pid d p resident
      have finalDevice := exactClear g ambient result out after device run
      intro target
      rw [finalDevice]
      by_cases same : pid = target
      · subst target
        simp [Config.expiryZeroDevice,Config.withPeer,Config.zeroedHandshake,
          responseTagMap,HANDSHAKE_ZEROED]
      · simpa [Config.expiryZeroDevice,Config.withPeer,Config.zeroedHandshake,
          responseTagMap,device,Std.TreeMap.getElem?_insert,same] using congrFun pre target

/-- The actual expiry clock and optional invalidations preserve all off-target
tags after handshake clearing. No record, key residency or alias premise. -/
theorem expireCurrentPeerKeypairs_tagMap (pid : PeerId) (entry : Option Device) :
    Ensures (expireCurrentPeerKeypairs pid) (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => ∀target, responseTagMap g.dev target =
        if pid = target then some HANDSHAKE_ZEROED else responseTagMap entry target) := by
  intro g ambient result out after pre run
  cases device : g.dev with
  | none =>
    simp [expireCurrentPeerKeypairs,requireNotPending,handshakeClear,
      IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [expireCurrentPeerKeypairs,requireNotPending,handshakeClear,
        IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨now,finalDevice⟩ := Config.expireCurrent_exact pid d p resident
        g ambient result out after device run
      intro target
      rw [finalDevice]
      simp only [Config.expiredDevice,invalidateDevice_tagMap]
      by_cases same : pid = target
      · subst target
        simp [Config.expiryHeadDevice,Config.withPeer,Config.zeroedHandshake,
          responseTagMap,HANDSHAKE_ZEROED]
      · simpa [Config.expiryHeadDevice,Config.withPeer,Config.zeroedHandshake,
          responseTagMap,device,Std.TreeMap.getElem?_insert,same] using congrFun pre target

end Leanux.Proofs.WG.Noise
