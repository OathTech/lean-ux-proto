import Image

open Lean Elab Term

/-- Elaborate a literal partial decoder entry. A parser rejection remains
`none`, so reaching that PC fails the fetched-instruction semantics. This is
the existing external decoding boundary, not a proof of the text parser. -/
elab "literalInstruction(" assembly:str ")" : term => do
  let instruction : Option Instr := match Kraken.X64.Parser.parse assembly.getString with
    | .ok [.instr i] => some i
    | .ok _ | .error _ => none
  return Lean.toExpr instruction
