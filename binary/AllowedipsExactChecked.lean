import AllowedipsReassignHeap

namespace Binary.Pair.Allowedips.Exact
open Leanux Leanux.WG
open Binary.Pair.Allowedips.Model

/-- The footprint frames bytes, rather than adding unchanged bytes to R. -/
def Writes (names : Names) (base : Nat) (a : BitVec 64) : Prop :=
  InRange (.ofNat 64 base) 8 a ∨ ListWrites names a

theorem effect_frame {names o s memory regs d id base node pid peer owner}
    (related : Corresponds names o s.dmem d) (shape : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer)
    (checked : effect s=.ok (memory,regs)) : EqualOutside (Writes names base) s.dmem memory := by
  have listFrame := effect_list_frame related shape named present peerNamed hasPeer nodeAt peerAt checked
  intro a outside
  exact (write64_frame s.dmem base peer a (fun inside => outside (.inl inside))).trans
    (listFrame a (fun inside => outside (.inr inside)))

local instance : Labels := Image.linkedLabels

/-- The tested segment reestablishes both reconstruction and its executable
heap assertion, and exports a byte frame for the next segment. -/
theorem assignment_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {names o s memory regs k d ambient id base node pid peer owner}
    (hasDevice : k.dev=some d)
    (related : Corresponds names o s.dmem d) (shape : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer)
    (checked : effect s=.ok (memory,regs)) :
    ∃ finalWG finalAmbient, ((assignment id pid).run k).run ambient=.ok (((),finalWG),finalAmbient) ∧
      Eventually (instructionStep fetch) (fun t =>
        t.pc=AllowedipsMutationImage.Add.entry+0x549 ∧ t.data.regs=regs ∧ t.data.dmem=memory ∧
        EqualOutside (Writes names base) s.dmem t.data.dmem ∧
        ∃ finalDevice, finalWG.dev=some finalDevice ∧ Corresponds names o t.data.dmem finalDevice ∧
          heap names (target finalDevice) t.data.dmem=.ok ())
        ⟨s,AllowedipsMutationImage.Add.entry+0x3e5⟩ := by
  obtain ⟨a,run⟩ := assignment_run k d ambient id pid node owner hasDevice present hasPeer
  refine ⟨{k with dev := some (exactInstalled d id node pid owner)},a,run,?_⟩
  have finalRelation := effect_corresponds related shape named present peerNamed hasPeer nodeAt peerAt checked
  have finalHeap := effect_heap related shape named present peerNamed hasPeer nodeAt peerAt checked
  rw [←target_exactInstalled d id pid node owner present hasPeer] at finalHeap
  have frame := effect_frame related shape named present peerNamed hasPeer nodeAt peerAt checked
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (effect_segment fetch decoder checked)
  rintro t ⟨pc,mem,reg⟩
  exact ⟨pc,reg,mem,by simpa only [mem] using frame,_,rfl,
    by simpa only [mem] using finalRelation,by simpa only [mem] using finalHeap⟩

#print axioms assignment_checked
end Binary.Pair.Allowedips.Exact
