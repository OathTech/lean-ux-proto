import RegionExecution

/-- Prove a concrete decoded layout one instruction at a time. Each cons
checks positive size, exact fetch and the existing supported-operation lemma.
Only the tail recurses; a wrong fetch or unsupported operation fails here. -/
syntax "binary_layout" : tactic

macro_rules
  | `(tactic| binary_layout) => `(tactic|
      first
      | exact Binary.LaidOut.nil _
      | (apply Binary.LaidOut.cons
         · decide
         · rfl
         · exact Binary.regular_mono _ _ _ True.intro
         · binary_layout))
