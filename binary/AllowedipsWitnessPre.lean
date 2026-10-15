import AllowedipsWitnessSeparation
import AllowedipsWitnessMapped
namespace Binary.AllowedipsWitness
open TrustBase AllowedipsRelation
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem entry (wide : Bool) : AllowedipsEntry (config wide) coverage 512 0x500000 (start wide) world view := by
  refine {
    pc := by cases wide <;> rfl
    entry := ?_
    root := by cases wide <;> rfl
    bits := by cases wide <;> rfl
    projection := by cases wide; exact project4; exact project6
    related := by cases wide; exact related4; exact related6
    focusNode := ?_
    focusPeer := by cases wide <;> rfl
    input := by cases wide; exact key4_read; exact key6_read
    stack := ?_
    preemptField := ?_
    coverageBefore := ?_
    coverageDuring := ?_
    hardirq := by decide
    pending := ?_
    stackData := ?_
    stackInput := ?_
    stackServices := ?_
    bufferData := ?_
    bufferInput := ?_
    bufferStack := ?_
    bufferMetadata := ?_
    bufferPreempt := ?_
    countStack := ?_
    countTrie := ?_
    countServices := ?_
    preemptData := ?_
    preemptStack := ?_
    preemptServices := ?_ }
  · cases wide
    · exact ⟨by decide, return_read 32 key4 (by decide)⟩
    · exact ⟨by decide, return_read 128 key6 (by decide)⟩
  · cases wide
    · exact (congrArg Option.join selected4).symm
    · exact (congrArg Option.join selected6).symm
  · intro i hi
    cases wide
    · exact stack_mapped 32 key4 i hi
    · exact stack_mapped 128 key6 i hi
  · cases wide
    · exact congrArg (Option.map (BitVec.ofInt 32)) (preempt_read 32 key4 (by decide))
    · exact congrArg (Option.map (BitVec.ofInt 32)) (preempt_read 128 key6 (by decide))
  · cases wide
    · exact coverage_at 32 key4 512
    · exact coverage_at 128 key6 512
  · cases wide
    · exact coverage_at 32 key4 (512+512)
    · exact coverage_at 128 key6 (512+512)
  · intro _
    cases wide
    · exact pending_read 32 key4
    · exact pending_read 128 key6
  · intro a read write
    have r := reads_location wide a read
    have w := stack_location wide a write
    omega
  · intro a read write
    have r := input_location wide a read
    have w := stack_location wide a write
    omega
  · intro a read write
    have w := stack_location wide a write
    rcases read with service | preempt
    · have r := service_location a service
      unfold ServiceLocation at r
      omega
    · have r := preempt_location a preempt
      omega
  · intro a read write
    have r := reads_location wide a read
    have w := buffer_location a write.2
    omega
  · intro a read write
    have r := input_location wide a read
    have w := buffer_location a write.2
    omega
  · intro a write stack
    have w := buffer_location a write.2
    have r := live_stack_location wide a stack
    omega
  · intro a write metadata
    have w := buffer_location a write.2
    have r := metadata_location a metadata
    unfold MetadataLocation at r
    omega
  · intro a write preempt
    have w := buffer_location a write.2
    have r := preempt_location a preempt
    omega
  · intro a write stack
    have w := count_location wide a write
    have r := live_stack_location wide a stack
    omega
  · intro a write trie
    have w := count_location wide a write
    have r := trie_location wide a trie
    omega
  · intro a write read
    have w := count_location wide a write
    rcases read with service | preempt
    · have r := service_location a service
      unfold ServiceLocation at r
      omega
    · have r := preempt_location a preempt
      omega
  · intro a read preempt
    have r := reads_location wide a read
    have w := preempt_location a preempt
    omega
  · intro a stack preempt
    have r := live_stack_location wide a stack
    have w := preempt_location a preempt
    omega
  · intro a service preempt
    have r := service_location a service
    have w := preempt_location a preempt
    unfold ServiceLocation at r
    omega

theorem pre4 : Pre_allowedips config4 coverage 512 0x500000 initial4 world := ⟨view, entry false⟩
theorem pre6 : Pre_allowedips config6 coverage 512 0x500000 initial6 world := ⟨view, entry true⟩

#print axioms pre4
#print axioms pre6
end Binary.AllowedipsWitness
