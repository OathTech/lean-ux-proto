import Leanux.Proofs.WG.Noise.ResponseEdgeFrames
import Leanux.Proofs.WG.Roaming.ResponseLookupSource
import Leanux.Proofs.WG.Index.LookupProvenanceSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do Roaming

/-- The successful response prefix reads the tag already present at entry.
The device is optional and there is no owner/reference coherence assumption. -/
theorem responseLookupPrefix_entry_tag (msg : List UInt8) (initial : Option Device) :
    Ensures (responseLookupPrefix msg) (fun g => g.dev = initial)
      (fun out _ => ∀ cut, out = some cut →
        ((initial.bind fun d => d.peers[cut.input.pid]?).map Peer.handshakeState) =
          some cut.input.peer.handshakeState) := by
  let R : Option ResponseLookupCut → WGWorld → Prop := fun out _ =>
    ∀ cut, out = some cut →
      ((initial.bind fun d => d.peers[cut.input.pid]?).map Peer.handshakeState) =
        some cut.input.peer.handshakeState
  have hnone (P : WGWorld → Prop) :
      Ensures (pure none : WG.M (Option ResponseLookupCut)) P R := by
    intro g ambient result final after _ run
    cases run
    intro cut impossible
    cases impossible
  have hfail (pid : PeerId) (P : WGWorld → Prop) :
      Ensures (do peerPut (some pid); pure none : WG.M _) P R := by
    refine ensures_bind (Q := fun _ _ => True) _ _ ?_ (fun _ => hnone _)
    intro _ _ _ _ _ _ _
    trivial
  have hbranch {α : Type} (site : Decision) (value : Bool) (next : Bool → WG.M α)
      (P : WGWorld → Prop) (Q : α → WGWorld → Prop)
      (hnext : Ensures (next value) P Q) :
      Ensures ((branch site value : WG.M Bool) >>= next) P Q := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (Config.branch_state_spec P site value)) ?_
    intro found g ambient result final after pre run
    rcases pre with ⟨rfl, pre⟩
    exact hnext g ambient result final after pre run
  have hdev : Ensures getDev (fun g => g.dev = initial)
      (fun d g => initial = some d ∧ g.dev = some d) := by
    intro g ambient d final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some found =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨pre.symm.trans device, device⟩
  have hread (d : Device) : Ensures (responseLookupRead msg)
      (fun g => initial = some d ∧ g.dev = some d)
      (fun out g => out.after.wg.device = g.dev ∧
        ∀ owner pid, out.entry = some (owner, pid) →
          (initial.bind fun d => d.peers[pid]?).map Peer.handshakeState =
            out.after.tagAt pid) := by
    intro g ambient out final after pre run
    change (((indexLookup [.handshake] (u32le msg 8)).run g).run ambient >>= fun ((entry, current), last) =>
      Except.ok ((ResponseLookupRead.mk (Campaign2.snapshot g ambient)
        (Campaign2.observeResult (((indexLookup [.handshake] (u32le msg 8)).run g).run ambient)) entry
        (Campaign2.snapshot current last), current), last)) = _ at run
    cases lookup : ((indexLookup [.handshake] (u32le msg 8)).run g).run ambient with
    | error err => rw [lookup] at run; cases run
    | ok pair =>
      rcases pair with ⟨⟨entry, current⟩, last⟩
      rw [lookup] at run
      cases run
      refine ⟨rfl, ?_⟩
      intro owner pid returned
      obtain ⟨_, _, _, p, resident, _, _, effect⟩ :=
        Index.indexLookup_success [.handshake] (u32le msg 8) d
          g ambient entry final after pre.2 lookup owner pid returned
      change (initial.bind fun d => d.peers[pid]?).map Peer.handshakeState =
        (final.dev.bind fun d => d.peers[pid]?).map Peer.handshakeState
      rw [pre.1, effect]
      simp only [Option.bind_some]
      rw [resident]
      exact (lookup_acquire_owner_tag d owner pid p).symm
  change Ensures _ _ R
  unfold responseLookupPrefix
  refine ensures_bind _ _ hdev ?_
  intro d
  refine hbranch _ _ _ _ _ ?_
  cases identity : d.staticIdentity.hasIdentity with
  | false => simpa [identity] using hnone (fun g => initial = some d ∧ g.dev = some d)
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine ensures_bind _ _ (hread d) ?_
    intro lookup
    refine hbranch _ _ _ _ _ ?_
    cases entry : lookup.entry with
    | none => simp only [Option.isNone_none, ↓reduceIte]; exact hnone _
    | some pair =>
      rcases pair with ⟨owner, pid⟩
      cases owner with
      | keypair id =>
        simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
        intro g ambient result final after _ run
        simp [invariant, AmbientM.invariant] at run
        cases run
      | handshake owner =>
        simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid _)) ?_
        intro p
        refine hbranch _ _ _ _ _ ?_
        by_cases created : p.handshakeState = HANDSHAKE_CREATED_INITIATION
        · simp only [created, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          intro g ambient result final after pre run
          cases run
          intro cut same
          cases same
          rcases pre with ⟨⟨device, tags⟩, resident⟩
          have tag := tags (.handshake owner) pid rfl
          change (initial.bind fun d => d.peers[pid]?).map Peer.handshakeState = _
          rw [tag]
          change (lookup.after.wg.device.bind fun d => d.peers[pid]?).map Peer.handshakeState = _
          rw [device]
          change (peerAt g pid).map Peer.handshakeState = _
          rw [resident]
          rfl
        · simp only [bne, beq_eq_false_iff_ne.mpr created, Bool.not_false, ↓reduceIte]
          exact hfail pid _
end Leanux.Proofs.WG.Noise
