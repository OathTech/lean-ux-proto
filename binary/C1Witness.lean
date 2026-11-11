import C1Joined
import C1ServiceHistory
import C1WitnessContract
import C1WitnessMemory
import C1WitnessMirror

/-! Result C1, open proposition `WitnessHolds` (`C1Interfaces`): closed.

The witness is the common decoder `Joint.fetch` with the active stub of
`C1WitnessStub` at the two service addresses, package 4's layout and
allocator state with a 16-byte scratch, and the concrete scene of
`C1WitnessScene`.

* `Premises` and `CallbacksFromImage`: package 4's `premises_of_contract`
  from the stub's contract (`C1WitnessContract.contract`).
* `ServiceActive`: the stub's own run from `serviceEntry`
  (`C1WitnessContract.alloc_active`), whose readiness is the caller's
  conditions of the first insertion (`C1WitnessMemory.service_ready`).
* `Executed`: the headline's steps at this decoder, one call after another;
  each next entry state takes its heap bytes from the previous final memory
  (`over`), so `Framed` carries the invariant across. The mirror's four runs
  are the evaluations of `C1WitnessMirror`.
 -/
namespace Binary.Statements.C1.Witness
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.Statements.C1.Proof
local instance : Labels := Image.linkedLabels

/-- The witness's decoder: the image's callbacks and WireGuard functions, and
the active stub at the two service addresses. -/
def code : Int64 → Option Decoded := Joint.fetch Witness.fetch

theorem tracePc : TracePcContract code := Callback.pc_contract _ Joint.services_agree

theorem stub_contract : AllocatorContract code L allocator :=
  contract (Joint.stub_agrees within) tracePc tableAt peers

/-- Every premise, and the callbacks from the image. -/
theorem premises : Premises code L allocator ∧ CallbacksFromImage code :=
  premises_of_contract within stub_contract

/-! ## The active service -/

theorem serviceActive : ServiceActive code L allocator := by
  have saved : serviceEntry.data.dmem.loadInt (serviceEntry.data.regs.rsp.toBitVec - 8) 8 ≠
      some (serviceEntry.data.regs.rdi.toNat : Int) := by
    have read : serviceEntry.data.dmem.loadInt (serviceEntry.data.regs.rsp.toBitVec - 8) 8 = some 0 :=
      service_saved
    rw [read]
    decide
  have run := alloc_active (Joint.stub_agrees within) tracePc tableAt peers c serviceEntry site []
    (outcome 77 true) [outcome 78 true, outcome 79 true, outcome 78 true, outcome 79 false]
    rfl service_frame service_ready (by decide) base_idle needed rfl 0 service_header (by decide) saved
  obtain ⟨t,history,ran,-,scratch,buffer⟩ := ran_of_eventually run (fun _ post => post.1)
  exact ⟨by decide,c,serviceEntry,t,site,[],outcome 77 true,
    [outcome 78 true, outcome 79 true, outcome 78 true, outcome 79 false],history,
    rfl,service_frame,service_ready,by decide,by decide,by decide,base_idle,needed,rfl,ran,scratch,buffer⟩

/-! ## The four calls -/

/-- The little-endian value of a list of bytes is below 256 to its length. -/
theorem bytes_bound : ∀ (bytes : List UInt8) (k : Nat),
    ((bytes.zipIdx k).map fun (b,i) => b.toNat * 256^i).sum + 256^k ≤ 256^(k + bytes.length)
  | [], k => by simp
  | b :: rest, k => by
    have tail := bytes_bound rest (k+1)
    have scaled : (b.toNat + 1) * 256^k ≤ 256 * 256^k :=
      Nat.mul_le_mul_right _ (by have := b.toNat_lt; omega)
    have next : 256^(k+1) = 256 * 256^k := by rw [Nat.pow_succ, Nat.mul_comm]
    have total : k + (b :: rest).length = k + 1 + rest.length := by simp only [List.length_cons]; omega
    have unfolded : (((b :: rest).zipIdx k).map fun (b,i) => b.toNat * 256^i).sum =
        b.toNat * 256^k + ((rest.zipIdx (k+1)).map fun (b,i) => b.toNat * 256^i).sum := rfl
    rw [unfolded, total]
    rw [next] at tail
    rw [Nat.add_mul, Nat.one_mul] at scaled
    generalize ((rest.zipIdx (k+1)).map fun (b,i) => b.toNat * 256^i).sum = rest' at tail ⊢
    generalize 256^(k + 1 + rest.length) = top at tail ⊢
    generalize 256^k = unit at tail scaled ⊢
    generalize b.toNat * unit = low at scaled ⊢
    omega

/-- An accepted eight-byte `word` read is a mapped range. -/
theorem word_read {m : Mem 64} {path : String} {a raw : Nat} (read : word m path a 8 = .ok raw) :
    ∃ bytes, m.loadBytes (.ofNat 64 a) 8 = some bytes := by
  unfold word at read
  split at read
  · cases loaded : m.loadBytes (.ofNat 64 a) 8 with
    | none => rw [loaded] at read; cases read
    | some bytes => exact ⟨bytes,rfl⟩
  · cases read

/-- `readNat` of a mapped range. -/
theorem readNat_of {m : Mem 64} {a : Nat} {bytes : List UInt8}
    (loaded : m.loadBytes (.ofNat 64 a) 8 = some bytes) :
    readNat ⟨{dmem := m},0⟩ a 8 = .ok (bytes.zipIdx.map fun (b,i) => b.toNat * 256^i).sum := by
  simp only [readNat, loaded]
  rfl

/-- The root word of the table is readable in any memory the invariant holds of. -/
theorem root_read {w : World} {m : Mem 64} (inv : Inv L allocator w m) :
    ∃ root, root < 2^64 ∧ readNat ⟨{dmem := m},0⟩ (L.table+AllowedipsMutationLayout.root4) 8 = .ok root := by
  obtain ⟨names,stream,table,-,asserted,-⟩ := inv
  obtain ⟨d,-,related,-⟩ := Allowedips.assertAt_ok asserted
  obtain ⟨raw,read,-⟩ := (Allowedips.reconstruct_fields related).root4
  rw [table] at read
  obtain ⟨bytes,loaded⟩ := word_read read
  have length := ((MemoryBytes.loadBytes_iff m _ 8 bytes).mp loaded).1
  have bound := bytes_bound bytes 0
  rw [length] at bound
  exact ⟨_,by omega,readNat_of loaded⟩

theorem five_sites : ∀ record ∈ five ++ [], record.site ∈ allocSites.map (·.2) := by decide

theorem executed (headline : HeadlineFor) : Executed code L allocator := by
  obtain ⟨initial,framed,insertStep,lookupStep⟩ := headline code L allocator premises.1
  obtain ⟨d0,device0,empty⟩ := base_empty
  have idle : allocator.Idle base [] (five ++ []) := base_idle
  have inv0 : Inv L allocator world base :=
    initial world d0 base (five ++ []) device0 world_armed world_hidden five_sites empty idle
  -- the root insertion
  obtain ⟨t1,h1,ran1,-,-,-,inv1,-⟩ := ran_of_eventually
    (insertStep c (insertEntry base 0 24 0x600000) world world1 4 0x0a000000 24 0 ra 0 inv0
      insert_ready_first run_first) (fun _ post => post.1)
  -- the insertion that allocates twice
  have entry2 : Inv L allocator world1 (over t1.data.dmem) :=
    framed world1 t1.data.dmem _ inv1 (over_heap t1.data.dmem)
  obtain ⟨t2,h2,ran2,-,-,-,inv2,-⟩ := ran_of_eventually
    (insertStep c (insertEntry (over t1.data.dmem) 1 32 0x601000) world1 world2 4 0x0b000001 32 1 ra 0
      entry2 (insert_ready_second _) run_second) (fun _ post => post.1)
  -- the insertion whose second allocation is refused
  have entry3 : Inv L allocator world2 (over t2.data.dmem) :=
    framed world2 t2.data.dmem _ inv2 (over_heap t2.data.dmem)
  obtain ⟨t3,h3,ran3,-,-,-,inv3,-⟩ := ran_of_eventually
    (insertStep c (insertEntry (over t2.data.dmem) 2 32 0x600000) world2 world3 4 0x0c000001 32 0 ra (-12)
      entry3 (insert_ready_third _) run_third) (fun _ post => post.1)
  -- the lookup
  have entry4 : Inv L allocator world3 (over t3.data.dmem) :=
    framed world3 t3.data.dmem _ inv3 (over_heap t3.data.dmem)
  obtain ⟨root,small,read⟩ := root_read inv3
  obtain ⟨d3,device3,root3At⟩ := device_third
  have found : (Source.lookup d3.peerAllowedips.root4 32 0x0a000005).run world3 = .ok (some 0,world4) := by
    rw [root3At]
    exact run_lookup
  obtain ⟨t4,h4,ran4,-⟩ := ran_of_eventually
    (lookupStep c (lookupEntry (over t3.data.dmem) root) world3 world4 d3 4 0x0a000005 ra (some 0) 0x600000
      entry4 device3 (lookup_ready _ root small read) found rfl) (fun _ post => post.1)
  exact ⟨world,world1,world2,world3,world4,d0,d3,c,c,c,c,
    insertEntry base 0 24 0x600000,t1,insertEntry (over t1.data.dmem) 1 32 0x601000,t2,
    insertEntry (over t2.data.dmem) 2 32 0x600000,t3,lookupEntry (over t3.data.dmem) root,t4,
    h1,h2,h3,h4,0x0a000000,24,0,0x0b000001,32,1,0x0c000001,32,0,0x0a000005,0x600000,0,ra,[],
    device0,world_armed,world_hidden,world_sites,empty,idle,insert_ready_first,run_first,ran1,
    over_heap t1.data.dmem,insert_ready_second _,run_second,hidden_second,ran2,
    over_heap t2.data.dmem,insert_ready_third _,run_third,hidden_third,ran3,
    over_heap t3.data.dmem,lookup_ready _ root small read,device3,found,rfl,ran4,needed⟩

#print axioms premises
#print axioms serviceActive
#print axioms executed
end Binary.Statements.C1.Witness

namespace Binary.Statements.C1.Proof
open Binary.Statements.C1 Binary.Statements.C1.Witness

/-- ACCEPTANCE. The witness of the final statement is inhabited: the active
stub meets every premise with the image's callbacks, the four calls run, and
the service uses its stack and writes the coverage buffer. -/
theorem witnessHolds : WitnessHolds :=
  fun headline => ⟨code,L,allocator,premises.1,premises.2,executed headline,serviceActive⟩

#print axioms witnessHolds
end Binary.Statements.C1.Proof
