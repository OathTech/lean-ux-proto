import LookupWitnessState

namespace Binary.LookupHitWitness
open Leanux Leanux.WG TrustBase

/-- The recorded handshake-owner read projection, with the count chosen as
    live (1) or zero. The zero-count variant is a domain witness, not a
    claim that this state was reached by the recorded kernel operation. -/
def count (live : Bool) : Nat := if live then 1 else 0

def peer (live : Bool) : Peer := {
  remoteStatic := [], presharedKey := [], precomputedStaticStatic := []
  internalId := 0, handshakeEntryPeer := some 0, refcount := count live }

def world (live : Bool) : World := {LookupWitness.world with
  k := {LookupWitness.world.k with wg := some {LookupWitness.device with
    peers := ({} : Std.TreeMap Nat Peer).insert 0 (peer live)}}}

def config : LookupRelation.Config := {LookupWitness.config with
  query := 0x0a0b0c0d, focus := ⟨some (.handshake 0), some 0⟩}

def view (live : Bool) : LookupRelation.View :=
  ⟨[LookupWitness.entry], some (some 0), some (count live)⟩

def memory (live : Bool) : Mem 64 :=
  ((LookupWitness.memory.storeInt 0x6000e0 8 0x600000).storeInt
    0x600420 4 (count live)).storeInt 0x300000 8 0

def data (live : Bool) : MachineData := {LookupWitness.data with
  dmem := memory live, regs := {LookupWitness.data.regs with rdx := 0x0a0b0c0d}}

def initial (live : Bool) : MachineState := ⟨data live, Image.Lookup.entry⟩

end Binary.LookupHitWitness
