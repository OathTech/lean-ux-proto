import LookupSourceFrame
import PairSequenceFacts

namespace Binary.Pair.Sequence
open Leanux Leanux.WG LookupSourceFrame
set_option maxRecDepth 2048

private theorem hidden_branch (d : Decision) (b : Bool) :
    Preserves World.hidden (branch d b) := by
  intro w answer final run
  cases run
  rfl

private theorem hidden_count (old : Nat) : Preserves World.hidden (refcountIncNotZero old) := by
  intro w answer final run
  have bound := PeerMirror.accepted_count_bound old w final answer run
  rw [PeerMirror.count_run old w bound] at run
  cases run
  unfold PeerMirror.countRecords
  split <;> rfl

private theorem hidden_peer (peer : Option PeerId) : Preserves World.hidden (peerGetMaybeZero peer) := by
  unfold peerGetMaybeZero
  apply preserves_bind (hidden_branch _ _)
  intro null
  cases null with
  | true => exact preserves_pure World.hidden _
  | false =>
    cases peer with
    | none => exact preserves_throw World.hidden _
    | some pid =>
      apply preserves_bind (preserves_pure World.hidden ())
      intro _
      apply preserves_bind (preserves_getPeer World.hidden pid)
      intro p
      apply preserves_bind (hidden_count p.refcount)
      intro live
      apply preserves_bind (hidden_branch _ _)
      intro dead
      cases dead with
      | true => exact preserves_pure World.hidden _
      | false =>
        apply preserves_bind (show Preserves World.hidden (setPeer pid {p with refcount := p.refcount+1}) from by
          intro w answer final run
          cases run
          rfl)
        intro _
        exact preserves_pure World.hidden _

private theorem hidden_owner_read (owner : IndexOwner) : Preserves World.hidden owner.peerWord := by
  cases owner with
  | handshake id => exact preserves_bind (preserves_getPeer World.hidden id) (fun _ => preserves_pure World.hidden _)
  | keypair id => exact preserves_bind (preserves_getKeypair World.hidden id) (fun _ => preserves_pure World.hidden _)

private theorem hidden_owner_write (owner : IndexOwner) (word : Option PeerId) :
    Preserves World.hidden (owner.setPeerWord word) := by
  cases owner with
  | handshake id =>
    apply preserves_bind (preserves_getPeer World.hidden id)
    intro p w answer final run
    cases run
    rfl
  | keypair id =>
    apply preserves_bind (preserves_getKeypair World.hidden id)
    intro p w answer final run
    cases run
    rfl

private theorem hidden_finish (a : LookupMirror.Acc) : Preserves World.hidden (LookupMirror.finish a) := by
  unfold LookupMirror.finish
  cases a.2 <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  all_goals try (apply preserves_bind (hidden_branch .idxWalk false); intro _)
  all_goals
    apply preserves_bind (hidden_branch _ _)
    intro found
    cases found with
    | false => exact preserves_pure World.hidden _
    | true =>
      cases a.1 with
      | none =>
        apply preserves_bind (preserves_throw World.hidden _)
        intro _
        exact preserves_pure World.hidden _
      | some e =>
        apply preserves_bind (hidden_owner_read e.owner)
        intro word
        apply preserves_bind (hidden_peer word)
        intro peer
        apply preserves_bind (hidden_owner_write e.owner peer)
        intro _
        apply preserves_bind (hidden_branch _ _)
        intro alive
        cases alive with
        | false => exact preserves_pure World.hidden _
        | true =>
          cases peer with
          | none =>
            apply preserves_bind (preserves_throw World.hidden _)
            intro _
            exact preserves_pure World.hidden _
          | some pid => exact preserves_pure World.hidden _

theorem lookup_input_frame {w final : World} {d : Device} {kinds query answer}
    (device : w.k.wg=some d) (run : (WG.indexLookup kinds query).run w=.ok (answer,final)) :
    final.hidden=w.hidden := by
  rw [LookupMirror.indexLookup_run kinds query w d device] at run
  have same := hidden_finish _ _ _ _ run
  have scan := congrArg World.hidden (LookupMirror.scan_world kinds query
    (d.indexTable.filter (fun e => e.index%8192==query%8192)) (none,false) w)
  exact same.trans scan

/-- Existing anchors do not consume the supplied random tape. This source
frame is separate from reconstruction and physical provider framing. -/
theorem input_frame {w final : World} {d : Device} {call answer}
    (device : w.k.wg=some d) (run : (source call).run w=.ok (answer,final)) :
    final.hidden=w.hidden := by
  cases call with
  | lookup query kinds =>
    change ((WG.indexLookup kinds query).run w >>= fun p => .ok (.lookup p.1,p.2))=.ok (answer,final) at run
    obtain ⟨⟨value,world⟩,first,equal⟩ := bind_ok run
    cases Except.ok.inj equal
    exact lookup_input_frame device first
  | remove owner =>
    change ((WG.indexRemove owner).run w >>= fun p => .ok (.remove,p.2))=.ok (answer,final) at run
    obtain ⟨⟨value,world⟩,first,equal⟩ := bind_ok run
    cases value
    cases Except.ok.inj equal
    rw [Remove.source_effect device first]
    rfl
  | replace pid kid =>
    change ((WG.indexReplaceHandshake pid kid).run w >>= fun p => .ok (.replace p.1,p.2))=.ok (answer,final) at run
    obtain ⟨⟨value,world⟩,first,equal⟩ := bind_ok run
    cases Except.ok.inj equal
    rw [(Replace.source_effect device first).2]
    rfl

#print axioms input_frame
end Binary.Pair.Sequence
