import PairLookupOtherFrame
import PairLookupPointer
import PairKeyedDecode
import PairLookupSource

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase LookupRelation CommonBitsCoverage Index
set_option maxRecDepth 2048
set_option maxHeartbeats 3000000

theorem reconstruct_after {n o coverage s w d query kinds ra after finalDevice}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (source : SourceFrame (callConfig n w d query kinds) d finalDevice)
    (allowed : ∀ owner, (callConfig n w d query kinds).focus.owner=some owner → ∀ value,
      OwnerWord.value finalDevice owner=some value → value=none ∨ value=(callConfig n w d query kinds).focus.peer)
    (physical : Sequential.At (callConfig n w d query kinds) after (callView (callConfig n w d query kinds) finalDevice))
    (frame : EqualOutside (LookupWrites (callConfig n w d query kinds) coverage.coverage coverage.preempt s.data
      (callView (callConfig n w d query kinds) d)) s.data.dmem after) : Corresponds n o after finalDevice := by
  let c := callConfig n w d query kinds
  have validation := (reconstruct_components facts.related).1
  have fields := validate_basic validation
  have layout := fields.1
  apply reconstruct_of_components validation
  · have buckets : (List.range 8192).mapM (decodeBucket n o after)=
        .ok ((List.range 8192).map fun b => finalDevice.indexTable.filter (fun e => e.index%8192==b)) := by
      apply mapM_values
      intro b member
      rw [source.table]
      exact (facts.shape_frame frame).bucket layout (List.mem_range.mp member)
        (reconstruct_bucket facts.related (List.mem_range.mp member))
    simpa only [target,Id.run,Pure.pure,Array.toList_map] using buckets
  · apply mapM_keyed Prod.fst Prod.fst ((owner_keys facts.related).trans source.owner_keys.symm)
    rintro ⟨owner,base⟩ named ⟨other,value⟩ member equal
    change owner=other at equal
    subst other
    have present := target_owner_iff.mp member
    by_cases focus : c.focus.owner=some owner
    · have endpoint := physical.2.2.1
      rw [focus] at endpoint
      obtain ⟨result,valueEq,wordAt⟩ := endpoint
      have same : value=result := by simpa only [callView,show (callConfig n w d query kinds).focus.owner=some owner from focus,Option.bind_some,present,Option.some.injEq] using valueEq
      subst result
      apply field_decode validation facts.storage facts.names named _ wordAt
      intro pid selected
      rcases allowed owner focus value present with zero | old
      · rw [zero] at selected; cases selected
      · have selectedPeer : c.focus.peer=some pid := old.symm.trans selected
        obtain ⟨peer,peerPresent⟩ := call_peer (w := w) (query := query) (kinds := kinds) facts.related selectedPeer
        obtain ⟨peerBase,peerNamed,_⟩ := peer_named facts.related peerPresent
        exact ⟨peerBase,peerNamed⟩
    · obtain ⟨old,raw,oldPresent,read,pointer⟩ := named_owner facts.related named
      have same : old=value := Option.some.inj (oldPresent.symm.trans ((source.owners owner focus).symm.trans present))
      subst old
      have unchanged := facts.owner_frame frame named focus s!"owner[{repr owner}].peer"
      have readAfter : word after s!"owner[{repr owner}].peer" (base+o.peer) 8=.ok raw := by
        simpa only [layout.peer,Nat.add_zero] using unchanged.symm.trans (by simpa only [layout.peer,Nat.add_zero] using read)
      change (do
        let raw ← word after s!"owner[{repr owner}].peer" (base+o.peer) 8
        return (owner,←peerId n s!"owner[{repr owner}].peer" raw))=.ok (owner,value)
      rw [readAfter]
      change (do let peer ← peerId n s!"owner[{repr owner}].peer" raw; pure (owner,peer))=.ok (owner,value)
      rw [pointer]; rfl
  · apply mapM_keyed Prod.fst Prod.fst ((count_keys facts.related).trans source.count_keys.symm)
    rintro ⟨id,base⟩ named ⟨other,count⟩ member equal
    change id=other at equal
    subst other
    obtain ⟨⟨pid,peer⟩,present,valueEq⟩ := List.mem_map.mp member
    obtain ⟨rfl,countEq⟩ := Prod.mk.inj valueEq
    have present : finalDevice.peers.get? pid=some peer := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp present
    have decoded : word after s!"peer[{pid}].refcount" (base+o.peerRefcount) 4=.ok count := by
      by_cases focus : c.focus.peer=some pid
      · have endpoint := physical.2.2.2
        rw [focus] at endpoint
        obtain ⟨number,valueAt,_,read⟩ := endpoint
        have numberEq : peer.refcount=number := by simpa only [callView,show (callConfig n w d query kinds).focus.peer=some pid from focus,Option.bind_some,present,Option.map_some,Option.some.injEq] using valueAt
        have bound := (storage_bounds facts.storage (count_storage named)).2
        have raw : after.loadInt (.ofNat 64 (base+o.peerRefcount)) 4=some (count : Int) := by
          change after.loadInt (Trie.interpretation n.peers pid+.ofNat 64 Layouts.peer_refcount) 4=some (number : Int) at read
          simpa only [Trie.interpretation_of_mem fields.2.2.2.1 named,←layout.peerRefcount,←BitVec.ofNat_add,
            ←numberEq,countEq] using read
        exact Trie.word_of_loadInt _ bound raw
      · obtain ⟨old,oldPresent,read⟩ := named_peer facts.related named
        have same := source.counts pid focus
        rw [present,oldPresent] at same
        have countSame : old.refcount=count := (Option.some.inj same).symm.trans countEq
        have unchanged := facts.count_frame frame named focus s!"peer[{pid}].refcount"
        rw [countSame] at read
        exact unchanged.symm.trans read
    change (do let value ← word after s!"peer[{pid}].refcount" (base+o.peerRefcount) 4; pure (pid,value))=.ok (pid,count)
    rw [decoded]; rfl

#print axioms reconstruct_after
end Binary.Pair.IndexLookup
