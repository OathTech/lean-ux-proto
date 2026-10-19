import SourceAdapter
import PairInsert
import PairRemoveWitnessState
import PairRandomRun

namespace Binary.Pair.Insert.Witness
open Leanux Leanux.WG TrustBase

abbrev names := Remove.Witness.names
abbrev offsets := Remove.Witness.offsets
abbrev device := Remove.Witness.device

def world (linked : Bool) : World := {Remove.Witness.world linked with ambient := {(Remove.Witness.world linked).ambient with hidden := some [record 7]}}
def context : CommonBitsCoverage.Context := ⟨⟨0x800000,0,0,0,0⟩,0⟩
def config : RandomProvider.Config := RandomRun.privateConfig

/-- Labelled synthetic witnesses. Both have a real initialized provider;
the linked case reinserts its owner from index zero to the cached draw seven. -/
def extraWords : List (Nat×Nat×Nat) :=
  [(0x8006e0,4,0),(RandomProvider.Layout.readyAddress,4,1),
   (RandomProvider.Layout.cacheAddress+96,8,1),(RandomProvider.Layout.cacheAddress,4,7),
   (RandomProvider.Layout.cpuAddress+32,8,1),(RandomProvider.Layout.baseAddress+32,8,1)]

def extraCells : List (BitVec 64 × UInt8) :=
  (extraWords.flatMap fun (a,size,value) =>
    (Int.toBytes size value).mapIdx (fun i b => (BitVec.ofNat 64 (a+i),b))) ++
  ((config.blocks++[(stackAddr-1080,1080)]).flatMap fun (a,size) =>
    (List.range size).map fun i => (BitVec.ofNat 64 (a+i),(0 : UInt8)))

def memory (linked : Bool) : DataMem :=
  extraCells.foldr (fun (a,b) m => m.insert a b) (Remove.Witness.memory linked)

def frameState (m : DataMem) : MachineState :=
  let base := Remove.Witness.frameState m
  {base with pc := .ofNat entry,data := {base.data with system := {cpl := 0,bits := 512}}}

def state (linked : Bool) : MachineState := frameState (memory linked)

end Binary.Pair.Insert.Witness
