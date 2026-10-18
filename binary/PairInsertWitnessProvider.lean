import PairInsertWitnessFacts

namespace Binary.Pair.Insert.Witness
open Leanux Leanux.WG TrustBase Index RandomProvider.Layout
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private instance [DecidableEq α] (x : Except ε α) (v : α) : Decidable (x=.ok v) :=
  match x with
  | .error e => .isFalse (by intro h; cases h)
  | .ok actual => decidable_of_iff (actual=v) (by simp)

def providerCells (base size : Nat) : List UInt8 :=
  (List.range size).map fun i =>
    if base+i=readyAddress || base+i=cacheAddress+96 || base+i=cpuAddress+32 || base+i=baseAddress+32
    then 1 else if base+i=cacheAddress then 7 else 0

def providerImage : DataMem :=
  (((({} : DataMem) ∪ (providerCells baseAddress 40).At (.ofNat 64 baseAddress)) ∪
    (providerCells cpuAddress 40).At (.ofNat 64 cpuAddress)) ∪
    (providerCells cacheAddress 108).At (.ofNat 64 cacheAddress)) ∪
    (providerCells readyAddress 4).At (.ofNat 64 readyAddress)

theorem provider_length (base size : Nat) : (providerCells base size).length=size := by
  simp only [providerCells,List.length_map,List.length_range]

theorem provider_read (linked : Bool) (span : Nat×Nat) (member : span ∈ config.blocks) :
    byteList linked (.ofNat 64 span.1) span.2=some (providerCells span.1 span.2) := by
  have cases : span=(readyAddress,4) ∨ span=(cacheAddress,108) ∨
      span=(cpuAddress,40) ∨ span=(baseAddress,40) := by
    simpa only [config,RandomRun.privateConfig,List.mem_cons,List.not_mem_nil,or_false] using member
  rcases cases with rfl | rfl | rfl | rfl <;> cases linked <;> decide +kernel

theorem provider_snapshot (linked : Bool) (m : DataMem)
    (reads : ∀ a size, m.loadBytes a size=byteList linked a size) :
    RandomProvider.snapshot config.blocks m=some providerImage := by
  have read := provider_read linked
  simp only [config,RandomRun.privateConfig] at read ⊢
  simp only [RandomProvider.snapshot,reads,read (readyAddress,4) (by simp),read (cacheAddress,108) (by simp),
    read (cpuAddress,40) (by simp),read (baseAddress,40) (by simp),Option.pure_def,providerImage]
  rfl

theorem provider_image_load (a : BitVec 64) (size : Nat) :
    providerImage.loadBytes a size=
      ((List.range size).map fun i =>
        (((providerCells readyAddress 4)[((a+.ofNat 64 i)-.ofNat 64 readyAddress).toNat]?).or
        (((providerCells cacheAddress 108)[((a+.ofNat 64 i)-.ofNat 64 cacheAddress).toNat]?).or
        (((providerCells cpuAddress 40)[((a+.ofNat 64 i)-.ofNat 64 cpuAddress).toNat]?).or
         (providerCells baseAddress 40)[((a+.ofNat 64 i)-.ofNat 64 baseAddress).toNat]?)))).allSome := by
  simp only [Mem.loadBytes,providerImage,Std.ExtHashMap.get?_eq_getElem?,Std.ExtHashMap.getElem?_union,
    get?_At (providerCells readyAddress 4) (.ofNat 64 readyAddress) _ (by rw [provider_length]; decide),
    get?_At (providerCells cacheAddress 108) (.ofNat 64 cacheAddress) _ (by rw [provider_length]; decide),
    get?_At (providerCells cpuAddress 40) (.ofNat 64 cpuAddress) _ (by rw [provider_length]; decide),
    get?_At (providerCells baseAddress 40) (.ofNat 64 baseAddress) _ (by rw [provider_length]; decide),Std.ExtHashMap.getElem?_empty,Option.or_none]

theorem provider_initialized (m : DataMem)
    (reads : ∀ a size, m.loadBytes a size=providerImage.loadBytes a size) :
    RandomProvider.initialized m=.ok () := by
  simp only [RandomProvider.initialized,RandomProvider.read,RandomProvider.mapped,Mem.loadInt,
    reads,provider_image_load]
  decide +kernel

theorem private_for_memory (linked : Bool) (m : DataMem)
    (reads : ∀ a size, m.loadBytes a size=byteList linked a size) :
    RandomProvider.check config 0x800000 false m=.ok () := by
  unfold RandomProvider.check
  rw [provider_snapshot linked m reads]
  have ranges : config.blocks.all (fun (base,size) => 0<size && base+size≤2^64)=true := by decide +kernel
  rw [ranges]
  change (do RandomProvider.initialized providerImage; if false then RandomProvider.recording config providerImage 0x800000 else pure ())=.ok ()
  rw [provider_initialized providerImage (fun _ _ => rfl)]
  rfl

#print axioms private_for_memory
end Binary.Pair.Insert.Witness
