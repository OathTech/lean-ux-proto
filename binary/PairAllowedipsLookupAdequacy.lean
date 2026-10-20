import PairAllowedipsLookupCheck
import PairAllowedipsLookupFrame
import PairAllowedipsAssert
import PairAllowedipsHeapFrame

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels

theorem lookupWrites_cover (names : Names) (o : AllowedipsProbe.Offsets)
    (c : Context) (s : MachineState) : Covers (lookupWrites names o c s)
      (fun a => AllowedipsEntry.TotalWrites s c.coverage c.preempt a ∨ Trie.CountBytes names.trie o a) := by
  intro a written
  rcases written with ordinary | count
  · exact (Trie.callTotalWrites_cover s c).append_left a ordinary
  · exact (Trie.countSpans_cover names.trie o).append_right a count

/-- Reuse the complete lookup proof on the retained component heap. Roots,
sequence, parents and ownership lists are preserved by its physical write
frame; only the already-proved peer count effect changes reconstruction. -/
theorem lookup_checked (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (peerDecoder : AnchoredDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp1 : AllowedipsTraceCmp1Contract fetch)
    (cmp4 : AllowedipsTraceConstCmp4Contract fetch) (byte : AllowedipsTraceConstCmp1Contract fetch)
    (bh : AllowedipsBhEnableContract fetch)
    {names input coverage initial w d family key ra answer final}
    (device : w.wg.dev=some d)
    (checked : lookupBoundary names input coverage initial w family key ra=.ok ())
    (accepted : (Source.lookup (if family==4 then d.peerAllowedips.root4 else d.peerAllowedips.root6)
      (if family==4 then 32 else 128) key).run w=.ok (answer,final)) :
    Eventually (instructionStep fetch) (fun t =>
      AllowedipsTail.Post initial coverage.coverage coverage.preempt ra
        (.ofBitVec (AllowedipsRelation.pointer (Trie.interpretation names.trie.peers) answer)) t ∧
      (∃ d', final.wg.dev=some d' ∧ Corresponds names input.offsets t.data.dmem d' ∧
        heap names (target d') t.data.dmem=.ok ()) ∧
      EqualOutside (fun a => AllowedipsEntry.TotalWrites initial coverage.coverage coverage.preempt a ∨
        Trie.CountBytes names.trie input.offsets a) initial.data.dmem t.data.dmem) initial := by
  unfold lookupBoundary at checked
  obtain ⟨_,asserted,checked⟩ := bind_ok checked
  obtain ⟨d',device',related,shape⟩ := assertAt_ok asserted
  have equal : d'=d := Option.some.inj (device'.symm.trans device)
  subst d'
  rw [device] at checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨apart,checked⟩ := check_ok _ _ _ _ checked
  have run := Trie.lookup_checked fetch decoder peerDecoder callbacks cmp1 cmp4 byte bh checked accepted
  obtain ⟨_,_,selected,_,_,_,effect⟩ := Trie.lookup_effect device accepted
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨returned,⟨afterDevice,afterPresent,core⟩,frame⟩
  have untouched : ∀ span ∈ metadataSpans names input.offsets, ∀ a, span.contains a →
      ¬(AllowedipsEntry.TotalWrites initial coverage.coverage coverage.preempt a ∨
        Trie.CountBytes names.trie input.offsets a) := by
    intro span member a inside written
    obtain ⟨write,member',inside'⟩ := lookupWrites_cover names input.offsets coverage initial a written
    exact spansApart_sound apart member member' inside inside'
  have metadata := MetadataSame.of_frame names input.offsets frame untouched
  have shapeFinal : heap names (target d) t.data.dmem=.ok () :=
    (heap_frame names input.offsets (target d) frame untouched).symm.trans shape
  refine ⟨returned,⟨afterDevice,afterPresent,?_⟩,frame⟩
  cases selected with
  | none =>
    obtain ⟨_,finalDevice⟩ := effect
    have equal : afterDevice=d := Option.some.inj (afterPresent.symm.trans finalDevice)
    subst afterDevice
    exact ⟨reconstruct_miss related core metadata,shapeFinal⟩
  | some id =>
    obtain ⟨_,pid,peer,_,_,present,_,_,_,finalDevice⟩ := effect
    have equal : afterDevice={d with peers := d.peers.insert pid {peer with refcount := peer.refcount+1}} :=
      Option.some.inj (afterPresent.symm.trans finalDevice)
    subst afterDevice
    refine ⟨reconstruct_hit related present core metadata,?_⟩
    rw [target_mapCounts d pid (peer.refcount+1) peer present,heap_mapCounts]
    exact shapeFinal

#print axioms lookup_checked
end Binary.Pair.Allowedips
