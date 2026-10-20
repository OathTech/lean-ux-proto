import PairCallWitness

open Lean Binary Binary.Pair Binary.Pair.Trie

def run (input : AllowedipsProbe.Input) : Except String Json := do
  let input := {input with entryPreempt := 0}
  let mut reports := #[]
  for bits in [32,128] do
    for seed in [(0 : UInt64),0xffffffffffffffff] do
      let (_,_,report) ← lookupFrom Witness.names input seed (CallWitness.state bits)
        {coverageSize := 32} Witness.coverage #[] (Witness.world bits) (some 0) bits 1
      reports := reports.push (Json.mkObj [("bits",toJson bits),("seed",toJson seed.toNat),("result",report)])
  return Json.mkObj [("status",toJson "pass"),("runs",toJson reports)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-pair-call-witness INPUT.json"; return 1
  let parsed := Json.parse (← IO.FS.readFile path) >>= fromJson? (α := AllowedipsProbe.Input)
  match parsed >>= run with
  | .ok result => IO.println result.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
