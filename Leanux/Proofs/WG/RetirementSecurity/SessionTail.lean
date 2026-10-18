import Leanux.Proofs.WG.RetirementSecurity.SessionFrames

/-! Original session suffix accounting includes handshake zeroing, the
live-peer guard, actual insertion, owner dereference and index replacement.
A normal tail cannot report refusal after consuming its new-key loan. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes

def sessionSuffix (pid : PeerId) (key : KeypairId) : WG.M Bool := do
  _ ← IndexOwner.peerDeref (.handshake pid)
  if !(← liftIndex (indexReplaceHandshake pid key)) then
    unsupported "begin_session: the handshake entry was unhashed"
  return true

theorem session_suffix_account (pid : PeerId) (key : KeypairId) (p : Peer)
    (credits : Credits.Ledger) :
    Hoare (sessionSuffix pid key) (PeerAccount pid p credits)
      (fun result w => result = true ∧ PeerAccount pid p credits w) := by
  unfold sessionSuffix
  apply hoare_bind _ _ (indexOwner_peerDeref_preserves (.handshake pid) (PeerAccount pid p credits))
  intro _
  apply hoare_bind _ _ (index_peer_account (indexReplaceHandshake pid key) pid p credits)
  intro replaced
  cases replaced with
  | false =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b _ run
    simp [unsupported,AmbientM.unsupported] at run
    cases run
  | true => exact hoare_pure true (PeerAccount pid p credits)

theorem session_tail_account (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (newKey : Credits.Allocation) (remaining : Credits.Ledger) (k : Keypair)
    (aligned : loans.Aligned p)
    (account : PeerAccount pid p (newKey :: loans.credits ++ remaining) w)
    (resident : keyAt w newKey.slot = some k) (a b : Ambient)
    (run : ((SessionOrigin.tail pid newKey.slot).run w).run a = .ok ((result,v),b)) :
    result = true ∧ PeerAccount pid (rotatedPeer (zeroedPeer p) newKey.slot k.iAmTheInitiator)
      ((loans.rotate newKey k.iAmTheInitiator p.keypairNext.isSome).credits ++ remaining) v := by
  unfold SessionOrigin.tail SessionOrigin.tailWith at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨zeroResult,s1,a1,zeroRun,run⟩ := run
  cases zeroResult
  have zeroed := (hoare_iff_run_ambient _ _ _).mp
    (zero_peer_account pid p (newKey :: loans.credits ++ remaining)) w a () s1 a1 account zeroRun
  have keyAfterZero : keyAt s1 newKey.slot = some k := (zero_keyAt pid w s1 a a1 zeroRun newKey.slot).trans resident
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨readPeer,s2,a2,getRun,run⟩ := run
  obtain ⟨worldSame,ambientSame,d,device,stored⟩ := Origins.getPeer_return pid s1 s2 readPeer a1 a2 getRun
  subst s2
  subst a2
  have samePeer : readPeer = zeroedPeer p := by
    have actual : peerAt s1 pid = some readPeer := by simp [peerAt,device,stored]
    exact Option.some.inj (actual.symm.trans zeroed.1)
  subst readPeer
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨alive,s3,a3,guard,run⟩ := run
  have selected : alive = !(zeroedPeer p).isDead ∧ s3 = s1 ∧
      a3 = CounterWindow.record a1 .sessionAlive (!(zeroedPeer p).isDead) := by
    simpa [branch,CounterWindow.branch_run,eq_comm,and_assoc] using guard
  obtain ⟨value,worldSame,ambientSame⟩ := selected
  subst alive
  subst s3
  subst a3
  cases dead : (zeroedPeer p).isDead with
  | true =>
    simp [dead,unsupported,AmbientM.unsupported] at run
    cases run
  | false =>
    simp only [dead,Bool.not_false,↓reduceIte] at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨rotateResult,s4,a4,rotateRun,suffixRun⟩ := run
    cases rotateResult
    have rotated := rotation_account pid (zeroedPeer p) loans newKey remaining k
      aligned zeroed keyAfterZero _ a4 rotateRun
    exact (hoare_iff_run_ambient _ _ _).mp
      (session_suffix_account pid newKey.slot (rotatedPeer (zeroedPeer p) newKey.slot k.iAmTheInitiator)
        ((loans.rotate newKey k.iAmTheInitiator p.keypairNext.isSome).credits ++ remaining))
      s4 a4 result v b rotated suffixRun

end Leanux.Proofs.WG.RetirementSecurity
