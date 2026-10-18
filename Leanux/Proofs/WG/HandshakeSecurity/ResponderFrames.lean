import Leanux.Proofs.WG.HandshakeSecurity.ResponderProjection

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem current_peer_write (w : WGWorld) (d : Device) (pid : PeerId) (old p : Peer)
    (device : w.dev = some d) (resident : d.peers[pid]? = some old)
    (same : p.keypairCurrent = old.keypairCurrent) :
    current {w with dev := some {d with peers := d.peers.insert pid p}} = current w := by
  funext q
  by_cases equal : pid = q
  · subst q
    simp [current, device, resident, same]
  · simp [current, device, Std.TreeMap.getElem?_insert, equal]

theorem current_key_write (w : WGWorld) (d : Device) (kid : KeypairId) (old k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[kid]? = some old)
    (same : keyCore k = keyCore old) :
    current {w with dev := some {d with keypairs := d.keypairs.insert kid k}} = current w := by
  funext pid
  cases peer : d.peers[pid]? with
  | none => simp [current, device, peer]
  | some p =>
    cases slot : p.keypairCurrent with
    | none => simp [current, device, peer, slot]
    | some id =>
      by_cases equal : kid = id
      · subst id
        simp [current, device, peer, slot, resident, same]
      · simp [current, device, peer, slot, Std.TreeMap.getElem?_insert, equal]

/-- Borrowing a key changes only its reference count, so it cannot make a
responder allocation current or change the current allocation's send key. -/
theorem keypairGet_current (kp : Option KeypairId) : SameView current (keypairGet kp) := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  cases kp with
  | none =>
    simp [keypairGet, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact entry
  | some id =>
    cases device : w.dev with
    | none =>
      simp [keypairGet, getKeypair, getDev, device, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.keypairs[id]? with
      | none =>
        simp [keypairGet, getKeypair, getDev, device, resident, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at run
        cases run
      | some k =>
        simp only [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
          branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, refcountIncNotZero,
          unsupported, invariant, AmbientM.unsupported, AmbientM.invariant,
          StateT.run_bind] at run
        simp [device, resident] at run
        split at run <;> simp_all
        all_goals try split at run <;> simp_all
        all_goals try split at run <;> simp_all
        all_goals try split at run <;> simp_all
        all_goals first
          | (change (Except.error _ : Except Stop _) = _ at run; cases run)
          | (rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
             exact (current_key_write w d id k {k with refcount := k.refcount + 1}
               device resident rfl).trans entry)

/-- The original staged-queue splice leaves the selected current identity and
send material unchanged. Its old peer is read in this same native action. -/
theorem clear_staged_current (pid : PeerId) :
    SameView current (do let p ← getPeer pid; setPeer pid {p with staged := []}) := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  cases device : w.dev with
  | none =>
    simp [getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      simp [getPeer, getDev, setPeer, modifyDev, device, resident] at run
      obtain ⟨rfl, rfl⟩ := run
      exact (current_peer_write w d pid p {p with staged := []} device resident rfl).trans entry

theorem Authorized.frame {confirmed : List Nat} {w v : WGWorld}
    (before : Authorized confirmed w) (frame : current v = current w) : Authorized confirmed v := by
  intro pid core resident responder
  rw [frame] at resident
  exact before pid core resident responder

end Leanux.Proofs.WG.HandshakeSecurity.Responder
