import PairCapture

/-! Regression controls for the streaming endpoint comparison. The bytes
are deliberately small synthetic inputs, not captured execution evidence. -/
open Lean Binary.Pair.Capture

def registers : Registers := {
  rax := 1, rbx := 2, rcx := 3, rdx := 4, rsi := 5, rdi := 6,
  rsp := 0x2000, rbp := 7, r8 := 8, r9 := 9, r10 := 10, r11 := 11,
  r12 := 12, r13 := 13, r14 := 14, r15 := 15, rip := 0x3000, eflags := 2 }

def rejected (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"control admitted: {label}")
  | .error _ => pure ()

def main : IO UInt32 := do
  let first : Block := ⟨0x1000, #[1, 2, 3]⟩
  let overlap : Block := ⟨0x1001, #[2, 3]⟩
  let endpoint : Endpoint := ⟨registers, #[first, overlap]⟩
  let extent := checkReturnExtent
  liftE (extent #[first, overlap] #[first, overlap])
  rejected "empty return capture" (extent #[first, overlap] #[])
  rejected "missing return block" (extent #[first, overlap] #[first])
  rejected "truncated return block" (extent #[first] #[⟨0x1000, #[1, 2]⟩])
  rejected "relocated return block" (extent #[first] #[⟨0x1001, #[1, 2, 3]⟩])
  let actual ← liftE (registers.state (← liftE (loadMemory #[first])))
  unless (← liftE (compareEndpoint endpoint actual)) == 5 do
    throw (IO.userError "consistent overlapping capture did not compare all bytes")
  rejected "inconsistent overlap" (compareEndpoint
    {endpoint with blocks := #[first, ⟨0x1001, #[9, 3]⟩]} actual)
  rejected "unmapped byte" (compareEndpoint
    {endpoint with blocks := #[⟨0x1003, #[0]⟩]} actual)
  rejected "byte exceeds width" (compareEndpoint
    {endpoint with blocks := #[⟨0x1000, #[256]⟩]} actual)
  rejected "NULL block" (compareEndpoint
    {endpoint with blocks := #[⟨0, #[1]⟩]} actual)
  rejected "wrapping block" (compareEndpoint
    {endpoint with blocks := #[⟨2^64 - 1, #[1, 2]⟩]} actual)
  rejected "register exceeds width" (compareEndpoint
    {endpoint with registers := {registers with rax := 2^64}} actual)
  rejected "changed PC" (compareEndpoint
    {endpoint with registers := {registers with rip := registers.rip + 1}} actual)
  rejected "changed interrupt flag" (compareEndpoint
    {endpoint with registers := {registers with eflags := registers.eflags ^^^ 512}} actual)
  IO.println "PASS: complete return extent, consistent overlap and twelve invalid endpoint/extent controls"
  return 0
