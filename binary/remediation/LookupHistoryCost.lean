import ProbeSupport

/-! Bounded generated diagnostic for memory-history retention. This does not
capture Linux or establish admission. Run `all` and `none` in separate
processes to compare peak memory while executing the same stores. -/
open Lean

def main (args : List String) : IO UInt32 := do
  let [mode] := args | throw (IO.userError "usage: LookupHistoryCost all|none")
  unless mode == "all" || mode == "none" do throw (IO.userError "invalid retention mode")
  let memory : DataMem := (List.replicate 262144 (0 : UInt8)).At 0x100000
  let initial : MachineState := ⟨{dmem := memory, regs := {rax := 123, rbx := 0x100000}}, 0x1000⟩
  let _ : Labels := ⟨fun _ => 0⟩
  let [.instr instruction] ← liftE (Kraken.X64.Parser.parse "movq %rax, (%rbx)")
    | throw (IO.userError "expected one store instruction")
  let selected := if mode == "all" then none else some (#[] : Array Nat)
  let started ← IO.monoMsNow
  let mut run : Run := {state := initial, history := #[initial]}
  for _ in [:128] do
    run ← liftE (interpret 0 run instruction 0x1000 3 selected)
  unless (← liftE (readNat run.state 0x100000 8)) == 123 && run.writes.size == 128 do
    throw (IO.userError "store execution or access log differs")
  IO.println (Json.mkObj [("mode", toJson mode), ("bytes", toJson (262144 : Nat)),
    ("writes", toJson run.writes.size), ("retained_states", toJson run.history.size),
    ("elapsed_ms", toJson ((← IO.monoMsNow) - started))]).compress
  return 0
