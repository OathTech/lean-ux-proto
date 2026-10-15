import Leanux.Proofs.WG.Noise.ClearEffects
import Leanux.Proofs.WG.Index.Release

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Leanux.Proofs.WG.Config Std.Do

/-- Normal immediate release derives every prerequisite from its actual guards. -/
theorem clearPut_ready_of_run (id : KeypairId) (d : Device) :
    Ensures (keypairPut (some id) true) (fun w => w.k.wg = some d)
      (fun _ _ => ∃ k, d.keypairs[id]? = some k ∧ 0 < k.refcount ∧ k.peer ≠ none) := by
  rw [ensures_iff]
  noise_vcgen [keypairPut, IndexOwner.peerDeref, IndexOwner.peerWord,
    getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    refcountDecAndTest, branch, branchCmp, invariant, unsupported, indexRemove,
    _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals grind

theorem clearPut_returns {key : Option KeypairId} {d final : Device}
    (put : ClearPut key d final) :
    Returns (keypairPut key true) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some final) := by
  cases put with
  | null d =>
    rw [returns_iff]
    mvcgen [keypairPut, branch]
  | present d id k resident live word =>
    exact Index.keypairPut_exact id true d k resident live word

theorem clearPut_effect (key : Option KeypairId) (d : Device) :
    Ensures (keypairPut key true) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ ClearPut key d final) := by
  intro w result final pre run
  cases key with
  | none =>
    obtain ⟨r, after, execution, device⟩ := clearPut_returns (.null d) w pre
    rw [run] at execution
    cases execution
    exact ⟨d, device, .null d⟩
  | some id =>
    obtain ⟨k, resident, live, word⟩ := clearPut_ready_of_run id d w result final pre run
    obtain ⟨r, after, execution, device⟩ :=
      Index.keypairPut_exact id true d k resident live word w pre
    rw [run] at execution
    cases execution
    exact ⟨_, device, .present d id k resident live word⟩

theorem clearRead_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (getPeer pid) (fun w => w.k.wg = some d)
      (fun result w => result = p ∧ w.k.wg = some d) := by
  rw [returns_iff]
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals simp_all

theorem clearWrite_returns (pid : PeerId) (slot : ClearSlot) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (modifyPeer pid slot.clear) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (clearWrite d pid slot p)) := by
  rw [returns_iff]
  noise_vcgen [_private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [clearWrite]

theorem clearOne_effect (pid : PeerId) (slot : ClearSlot) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (clearOne pid slot.read slot.clear) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        ClearPut (slot.read p) (clearWrite d pid slot p) final) := by
  intro w result final pre run
  obtain ⟨r, afterRead, readRun, value, readDevice⟩ := clearRead_returns pid d p resident w pre
  subst r
  obtain ⟨u, afterWrite, writeRun, writeDevice⟩ :=
    clearWrite_returns pid slot d p resident afterRead readDevice
  simp only [clearOne, StateT.run_bind, readRun] at run
  change ((modifyPeer pid slot.clear).run afterRead >>= fun out =>
    (keypairPut (slot.read p) true).run out.2) = .ok (result, final) at run
  rw [writeRun] at run
  exact clearPut_effect (slot.read p) (clearWrite d pid slot p) afterWrite result final writeDevice run

/-- A proof-local sequence reuses the existing single-slot source unchanged. -/
def clearSequence (pid : PeerId) : List ClearSlot → M Unit
  | [] => pure ()
  | slot :: rest => do
    clearOne pid slot.read slot.clear
    clearSequence pid rest

theorem keypairsClear_sequence (pid : PeerId) :
    keypairsClear pid = clearSequence pid [.next, .previous, .current] := by
  rw [keypairsClear_source]
  simp [clearSequence]
  rfl

theorem clearSequence_effect (pid : PeerId) (slots : List ClearSlot) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (clearSequence pid slots) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ ClearRun pid d slots final) := by
  induction slots generalizing d p with
  | nil =>
    intro w result final pre run
    change Except.ok ((), w) = Except.ok (result, final) at run
    cases run
    exact ⟨d, pre, .nil d⟩
  | cons slot rest ih =>
    change Ensures (clearOne pid slot.read slot.clear >>= fun _ => clearSequence pid rest) _ _
    refine ensures_bind _ _ (clearOne_effect pid slot d p resident) ?_
    intro u w result final pre run
    obtain ⟨middle, device, put⟩ := pre
    have peer : middle.peers[pid]? = some (slot.clear p) := by
      rw [clearPut_peers put]
      simp [clearWrite]
    obtain ⟨out, output, tail⟩ := ih middle (slot.clear p) peer w result final device run
    exact ⟨out, output, .cons d slot p middle out rest resident put tail⟩

/-- Static readiness is consumed at one actual slot release. -/
theorem clearOne_returns_ready (pid : PeerId) (slot : ClearSlot) (d : Device) (p : Peer)
    (rest : List (Option KeypairId)) (resident : d.peers[pid]? = some p)
    (ready : ClearReady d (slot.read p :: rest)) :
    Returns (clearOne pid slot.read slot.clear) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        ClearPut (slot.read p) (clearWrite d pid slot p) final ∧
        final.peers[pid]? = some (slot.clear p) ∧ ClearReady final rest) := by
  intro w pre
  obtain ⟨r, afterRead, readRun, value, readDevice⟩ := clearRead_returns pid d p resident w pre
  subst r
  obtain ⟨u, afterWrite, writeRun, writeDevice⟩ :=
    clearWrite_returns pid slot d p resident afterRead readDevice
  obtain ⟨out, put, next⟩ := clearPut_exists (slot.read p) (clearWrite d pid slot p) rest ready
  obtain ⟨v, final, putRun, finalDevice⟩ := clearPut_returns put afterWrite writeDevice
  refine ⟨v, final, ?_, out, finalDevice, put, ?_, next⟩
  · simp only [clearOne, StateT.run_bind, readRun]
    change ((modifyPeer pid slot.clear).run afterRead >>= fun out =>
      (keypairPut (slot.read p) true).run out.2) = .ok (v, final)
    rw [writeRun]
    exact putRun
  · rw [clearPut_peers put]
    simp [clearWrite]

theorem keypairsClear_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (keypairsClear pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        ClearRun pid d [.next, .previous, .current] final) := by
  rw [keypairsClear_sequence]
  exact clearSequence_effect pid _ d p resident

/-- No records are needed: sufficient reference multiplicity guarantees every
release, including repeated slot identities, reaches its normal return. -/
theorem keypairsClear_returns_ready (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (ready : ClearReady d (clearKeys p)) :
    Returns (keypairsClear pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        ClearRun pid d [.next, .previous, .current] final) := by
  intro w pre
  obtain ⟨u1, w1, run1, d1, hd1, put1, peer1, ready1⟩ :=
    clearOne_returns_ready pid .next d p [p.keypairPrevious, p.keypairCurrent]
      resident ready w pre
  obtain ⟨u2, w2, run2, d2, hd2, put2, peer2, ready2⟩ :=
    clearOne_returns_ready pid .previous d1 (ClearSlot.next.clear p) [p.keypairCurrent]
      peer1 ready1 w1 hd1
  obtain ⟨u3, w3, run3, d3, hd3, put3, peer3, ready3⟩ :=
    clearOne_returns_ready pid .current d2 (ClearSlot.previous.clear (ClearSlot.next.clear p)) []
      peer2 ready2 w2 hd2
  cases u1; cases u2; cases u3
  refine ⟨(), w3, ?_, d3, hd3, ?_⟩
  · rw [keypairsClear_sequence]
    simp only [clearSequence, StateT.run_bind, run1]
    change ((clearOne pid ClearSlot.previous.read ClearSlot.previous.clear).run w1 >>= fun out =>
      (clearOne pid ClearSlot.current.read ClearSlot.current.clear >>= fun _ => pure ()).run out.2) = _
    rw [run2]
    change ((clearOne pid ClearSlot.current.read ClearSlot.current.clear).run w2 >>= fun out =>
      Except.ok ((), out.2)) = _
    rw [run3]
    rfl
  · exact .cons d .next p d1 d3 [.previous, .current] resident put1
      (.cons d1 .previous (ClearSlot.next.clear p) d2 d3 [.current] peer1 put2
        (.cons d2 .current (ClearSlot.previous.clear (ClearSlot.next.clear p)) d3 d3 [] peer2 put3 (.nil d3)))

end Leanux.Proofs.WG.Noise
