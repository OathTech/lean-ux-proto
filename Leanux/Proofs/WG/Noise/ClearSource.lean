import Leanux.Proofs.WG.Noise.ClearEffects
import Leanux.Proofs.WG.Index.Release
import Leanux.Proofs.WG.Noise.Slots

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Leanux.Proofs.WG.Config Std.Do

/-- Normal immediate release derives every prerequisite from its actual guards. -/
theorem clearPut_ready_of_run (id : KeypairId) (d : Device) :
    Ensures (keypairPut (some id) true) (fun w => w.dev = some d)
      (fun _ _ => ∃ k, d.keypairs[id]? = some k ∧ 0 < k.refcount ∧ k.peer ≠ none) := by
  intro g ambient result final after device run
  cases resident : d.keypairs[id]? with
  | none =>
    simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev,
      device, resident, invariant, AmbientM.invariant] at run
    cases run
  | some k =>
    cases peer : k.peer with
    | none =>
      simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev,
        device, resident, IndexOwner.peerDeref, IndexOwner.peerWord, peer,
        unsupported, AmbientM.unsupported] at run
      cases run
    | some owner =>
      refine ⟨k, rfl, ?_, by simp [peer]⟩
      by_cases positive : 0 < k.refcount
      · exact positive
      · exfalso
        have zero : k.refcount = 0 := by omega
        have removeForm : indexRemove (.keypair id) = (do
          _ ← branch .idxRemoveHashed ((← get).any (·.owner == .keypair id))
          modify fun table => table.filter fun e => !(e.owner == .keypair id) : IndexM Unit) := rfl
        have lifted : (monadLift (indexRemove (.keypair id)) : WG.M Unit) =
            liftIndex (indexRemove (.keypair id)) := rfl
        simp only [keypairPut, lifted] at run
        simp [branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
          getKeypair, getDev, device, resident, IndexOwner.peerDeref, IndexOwner.peerWord,
          peer, setKeypair, modifyDev, refcountDecAndTest, zero, removeForm, liftIndex,
          invariant, AmbientM.invariant, unsupported, AmbientM.unsupported] at run
        cases run

theorem clearPut_returns {key : Option KeypairId} {d final : Device}
    (put : ClearPut key d final) :
    Returns (keypairPut key true) (fun w => w.dev = some d)
      (fun _ w => w.dev = some final) := by
  cases put with
  | null d =>
    intro g ambient device
    exact ⟨(), g, _, rfl, device⟩
  | present d id k resident live word =>
    exact Index.keypairPut_exact id true d k resident live word

theorem clearPut_effect (key : Option KeypairId) (d : Device) :
    Ensures (keypairPut key true) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ ClearPut key d final) := by
  intro w ambient result final after pre run
  cases key with
  | none =>
    obtain ⟨r, next, nextAmbient, execution, device⟩ := clearPut_returns (.null d) w ambient pre
    rw [run] at execution
    cases execution
    exact ⟨d, device, .null d⟩
  | some id =>
    obtain ⟨k, resident, live, word⟩ := clearPut_ready_of_run id d w ambient result final after pre run
    obtain ⟨r, next, nextAmbient, execution, device⟩ :=
      Index.keypairPut_exact id true d k resident live word w ambient pre
    rw [run] at execution
    cases execution
    exact ⟨_, device, .present d id k resident live word⟩

theorem clearRead_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (getPeer pid) (fun w => w.dev = some d)
      (fun result w => result = p ∧ w.dev = some d) := by
  intro g ambient device
  refine ⟨p, g, ambient, ?_, rfl, device⟩
  simp [getPeer, getDev, device, resident]
  rfl

theorem clearWrite_returns (pid : PeerId) (slot : ClearSlot) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (modifyPeer pid slot.clear) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (clearWrite d pid slot p)) := by
  intro g ambient device
  refine ⟨(), {g with dev := some (clearWrite d pid slot p)}, ambient, ?_, rfl⟩
  change (((do let q ← getPeer pid; setPeer pid (slot.clear q)) : WG.M Unit).run g).run ambient = _
  simp [getPeer, getDev, device, resident, setPeer, modifyDev, clearWrite]
  rfl

theorem clearOne_effect (pid : PeerId) (slot : ClearSlot) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (clearOne pid slot.read slot.clear) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        ClearPut (slot.read p) (clearWrite d pid slot p) final) := by
  intro w ambient result final after pre run
  obtain ⟨r, afterRead, readAmbient, readRun, value, readDevice⟩ :=
    clearRead_returns pid d p resident w ambient pre
  subst r
  obtain ⟨u, afterWrite, writeAmbient, writeRun, writeDevice⟩ :=
    clearWrite_returns pid slot d p resident afterRead readAmbient readDevice
  change (((getPeer pid).run w).run ambient >>= fun ((q, g), a) =>
    (((modifyPeer pid slot.clear).run g).run a >>= fun ((_, g'), a') =>
      ((keypairPut (slot.read q) true).run g').run a')) = _ at run
  rw [readRun] at run
  change (((modifyPeer pid slot.clear).run afterRead).run readAmbient >>= fun ((_, g), a) =>
    ((keypairPut (slot.read p) true).run g).run a) = _ at run
  rw [writeRun] at run
  exact clearPut_effect (slot.read p) (clearWrite d pid slot p)
    afterWrite writeAmbient result final after writeDevice run

/-- A proof-local sequence reuses the existing single-slot source unchanged. -/
def clearSequence (pid : PeerId) : List ClearSlot → WG.M Unit
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
    Ensures (clearSequence pid slots) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ ClearRun pid d slots final) := by
  induction slots generalizing d p with
  | nil =>
    intro w ambient result final after pre run
    change Except.ok (((), w), ambient) = Except.ok ((result, final), after) at run
    cases run
    exact ⟨d, pre, .nil d⟩
  | cons slot rest ih =>
    change Ensures (clearOne pid slot.read slot.clear >>= fun _ => clearSequence pid rest) _ _
    refine ensures_bind _ _ (clearOne_effect pid slot d p resident) ?_
    intro u w ambient result final after pre run
    obtain ⟨middle, device, put⟩ := pre
    have peer : middle.peers[pid]? = some (slot.clear p) := by
      rw [clearPut_peers put]
      simp [clearWrite]
    obtain ⟨out, output, tail⟩ := ih middle (slot.clear p) peer w ambient result final after device run
    exact ⟨out, output, .cons d slot p middle out rest resident put tail⟩

/-- Static readiness is consumed at one actual slot release. -/
theorem clearOne_returns_ready (pid : PeerId) (slot : ClearSlot) (d : Device) (p : Peer)
    (rest : List (Option KeypairId)) (resident : d.peers[pid]? = some p)
    (ready : ClearReady d (slot.read p :: rest)) :
    Returns (clearOne pid slot.read slot.clear) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        ClearPut (slot.read p) (clearWrite d pid slot p) final ∧
        final.peers[pid]? = some (slot.clear p) ∧ ClearReady final rest) := by
  intro w ambient pre
  obtain ⟨r, afterRead, readAmbient, readRun, value, readDevice⟩ :=
    clearRead_returns pid d p resident w ambient pre
  subst r
  obtain ⟨u, afterWrite, writeAmbient, writeRun, writeDevice⟩ :=
    clearWrite_returns pid slot d p resident afterRead readAmbient readDevice
  obtain ⟨out, put, next⟩ := clearPut_exists (slot.read p) (clearWrite d pid slot p) rest ready
  obtain ⟨v, final, after, putRun, finalDevice⟩ :=
    clearPut_returns put afterWrite writeAmbient writeDevice
  refine ⟨v, final, after, ?_, out, finalDevice, put, ?_, next⟩
  · change (((getPeer pid).run w).run ambient >>= fun ((q, g), a) =>
      (((modifyPeer pid slot.clear).run g).run a >>= fun ((_, g'), a') =>
        ((keypairPut (slot.read q) true).run g').run a')) = _
    rw [readRun]
    change (((modifyPeer pid slot.clear).run afterRead).run readAmbient >>= fun ((_, g), a) =>
      ((keypairPut (slot.read p) true).run g).run a) = _
    rw [writeRun]
    exact putRun
  · rw [clearPut_peers put]
    simp [clearWrite]

theorem keypairsClear_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (keypairsClear pid) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        ClearRun pid d [.next, .previous, .current] final) := by
  rw [keypairsClear_sequence]
  exact clearSequence_effect pid _ d p resident

/-- No records are needed: sufficient reference multiplicity guarantees every
release, including repeated slot identities, reaches its normal return. -/
theorem keypairsClear_returns_ready (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (ready : ClearReady d (clearKeys p)) :
    Returns (keypairsClear pid) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        ClearRun pid d [.next, .previous, .current] final) := by
  intro w ambient pre
  obtain ⟨u1, w1, a1, run1, d1, hd1, put1, peer1, ready1⟩ :=
    clearOne_returns_ready pid .next d p [p.keypairPrevious, p.keypairCurrent]
      resident ready w ambient pre
  obtain ⟨u2, w2, a2, run2, d2, hd2, put2, peer2, ready2⟩ :=
    clearOne_returns_ready pid .previous d1 (ClearSlot.next.clear p) [p.keypairCurrent]
      peer1 ready1 w1 a1 hd1
  obtain ⟨u3, w3, a3, run3, d3, hd3, put3, peer3, ready3⟩ :=
    clearOne_returns_ready pid .current d2 (ClearSlot.previous.clear (ClearSlot.next.clear p)) []
      peer2 ready2 w2 a2 hd2
  cases u1; cases u2; cases u3
  refine ⟨(), w3, a3, ?_, d3, hd3, ?_⟩
  · rw [keypairsClear_sequence]
    change (((clearOne pid ClearSlot.next.read ClearSlot.next.clear).run w).run ambient >>=
      fun ((_, g), a) =>
        (((clearOne pid ClearSlot.previous.read ClearSlot.previous.clear).run g).run a >>=
          fun ((_, g'), a') =>
            (((clearOne pid ClearSlot.current.read ClearSlot.current.clear).run g').run a' >>=
              fun ((_, g''), a'') => Except.ok (((), g''), a'')))) = _
    rw [run1]
    change (((clearOne pid ClearSlot.previous.read ClearSlot.previous.clear).run w1).run a1 >>=
      fun ((_, g), a) =>
        (((clearOne pid ClearSlot.current.read ClearSlot.current.clear).run g).run a >>=
          fun ((_, g'), a') => Except.ok (((), g'), a'))) = _
    rw [run2]
    change (((clearOne pid ClearSlot.current.read ClearSlot.current.clear).run w2).run a2 >>=
      fun ((_, g), a) => Except.ok (((), g), a)) = _
    rw [run3]
    rfl
  · exact .cons d .next p d1 d3 [.previous, .current] resident put1
      (.cons d1 .previous (ClearSlot.next.clear p) d2 d3 [.current] peer1 put2
        (.cons d2 .current (ClearSlot.previous.clear (ClearSlot.next.clear p)) d3 d3 [] peer2 put3 (.nil d3)))

end Leanux.Proofs.WG.Noise
