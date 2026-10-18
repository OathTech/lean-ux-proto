import Execution
import Memory

namespace Binary.MemoryInvariant

/-- A memory invariant stable under ordinary RAM writes. No premise about
MMIO is needed: Kraken's `All` judgment rejects non-memory effects. -/
def StoreStable (F : DataMem → Prop) : Prop :=
  ∀ m a n v, F m → F (m.storeInt a n v)

def Keeps (F : DataMem → Prop) (e : Effects) : Prop :=
  e.All (fun _ => True) → e.All (fun t => F t.data.dmem)

variable {F : DataMem → Prop}

theorem load {s : MachineData} (hs : F s.dmem) (a w ret)
    (k : ∀ v t, F t.dmem → Keeps F (ret v t)) : Keeps F (s.load a w ret) := by
  unfold MachineData.load Keeps
  simp only [Effects.All]
  split
  · exact k _ _ hs
  · exact False.elim

theorem store (stable : StoreStable F) {s : MachineData} (hs : F s.dmem)
    (a) {w : Width} (v : w.type) (ret) (k : ∀ t, F t.dmem → Keeps F (ret t)) :
    Keeps F (s.store a v ret) := by
  unfold MachineData.store Keeps
  simp only [Effects.All]
  split
  · exact k _ (stable _ _ _ _ hs)
  · exact False.elim

theorem regMem [Labels] [AddressSize] {s : MachineData} (hs : F s.dmem)
    {w} (x : RegOrMem w) (p ret) (k : ∀ v t, F t.dmem → Keeps F (ret v t)) :
    Keeps F (x.interp s p ret) := by
  cases x with
  | reg r => exact k _ _ hs
  | mem a => exact load hs _ _ _ k

theorem reg {s : MachineData} (hs : F s.dmem) {w} (x : Reg w) (p ret)
    (k : ∀ v t, F t.dmem → Keeps F (ret v t)) : Keeps F (x.interp s p ret) := k _ _ hs

theorem operand [Labels] [AddressSize] {s : MachineData} (hs : F s.dmem)
    {w} (x : Operand w) (p ret) (k : ∀ v t, F t.dmem → Keeps F (ret v t)) :
    Keeps F (x.interp s p ret) := by
  cases x with
  | regOrMem x => exact regMem hs _ _ _ k
  | imm x => exact k _ _ hs

theorem relative [Labels] [AddressSize] {s : MachineData} (hs : F s.dmem)
    (x : RelRegOrMem) (p ret) (k : ∀ v t, F t.dmem → Keeps F (ret v t)) :
    Keeps F (x.interp s p ret) := by
  cases x with
  | rel x => exact k _ _ hs
  | reg x => exact k _ _ hs
  | mem a => exact load hs _ _ _ k

theorem set [Labels] [AddressSize] (stable : StoreStable F) {s : MachineData} (hs : F s.dmem)
    {w} (x : Dst w) (v p ret) (k : ∀ t, F t.dmem → Keeps F (ret t)) :
    Keeps F (s.set x v p ret) := by
  cases x with
  | reg r => exact k _ hs
  | mem a => exact store stable hs _ _ _ k

theorem undefined {α} [NondetSupportingType α] {k : α → Effects}
    (h : ∀ v, Keeps F (k v)) : Keeps F (.undefined k) := by
  intro success v
  exact h v (success v)

theorem impossible (s : String) : Keeps F (.unimplemented s) := False.elim

/-- Follow the interpreter's memory operations, without simplifying the
arithmetic they compute. All branches and undefined choices are retained. -/
theorem operation [Labels] [address_size : AddressSize] (stable : StoreStable F) {w}
    (i : Operation w) (p : Std.Rco Int64) (s : MachineData) (hs : F s.dmem)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
    (hn : ∀ t, F t.dmem → Keeps F (next t))
    (hj : ∀ pc t, F t.dmem → Keeps F (jmp pc t)) :
    Keeps F (i.interp p s next jmp) := by
  cases i <;> simp only [Operation.interp]
  all_goals first
    | exact hn _ hs
    | exact hj _ _ hs
    | skip
  all_goals repeat first
    | apply operand (by assumption); intro v t ht
    | apply regMem (by assumption); intro v t ht
    | apply reg (by assumption); intro v t ht
    | apply relative (by assumption); intro v t ht
    | apply load (by assumption); intro v t ht
    | apply set stable (by assumption); intro t ht
    | apply store stable (by assumption); intro t ht
    | apply undefined; intro v
    | exact impossible _
    | exact hn _ (by assumption)
    | exact hj _ _ (by assumption)
    | split

#print axioms operation

theorem loadAvx {s : MachineData} (hs : F s.dmem) (a w ret align)
    (k : ∀ v t, F t.dmem → Keeps F (ret v t)) : Keeps F (s.loadAvx a w ret align) := by
  unfold MachineData.loadAvx Keeps
  split
  · exact False.elim
  · simp only [Effects.All]
    split
    · exact k _ _ hs
    · exact False.elim

theorem storeAvx (stable : StoreStable F) {s : MachineData} (hs : F s.dmem)
    (a) {w : AvxWidth} (v : w.type) (ret align) (k : ∀ t, F t.dmem → Keeps F (ret t)) :
    Keeps F (s.storeAvx a v ret align) := by
  unfold MachineData.storeAvx Keeps
  split
  · exact False.elim
  · simp only [Effects.All]
    split
    · exact k _ (stable _ _ _ _ hs)
    · exact False.elim

theorem avxRegMem [Labels] [AddressSize] {s : MachineData} (hs : F s.dmem)
    {w} (x : AvxRegOrMem w) (p ret align) (k : ∀ v t, F t.dmem → Keeps F (ret v t)) :
    Keeps F (x.interp s p ret align) := by
  cases x with
  | avx r => exact k _ _ hs
  | mem a => exact loadAvx hs _ _ _ _ k

theorem avxOperand [Labels] [AddressSize] {s : MachineData} (hs : F s.dmem)
    {w} (x : AvxOperand w) (p ret align) (k : ∀ v t, F t.dmem → Keeps F (ret v t)) :
    Keeps F (x.interp s p ret align) := by
  cases x with
  | regOrMem x => exact avxRegMem hs _ _ _ _ k

theorem setAvx [Labels] [AddressSize] (stable : StoreStable F) {s : MachineData} (hs : F s.dmem)
    {w} (x : AvxDst w) (v p ret align) (k : ∀ t, F t.dmem → Keeps F (ret t)) :
    Keeps F (s.setAvx x v p ret align) := by
  cases x with
  | avx r => exact k _ hs
  | mem a => exact storeAvx stable hs _ _ _ _ k

theorem setAvxLegacy [Labels] [AddressSize] (stable : StoreStable F) {s : MachineData} (hs : F s.dmem)
    {w} (x : AvxDst w) (v p ret align) (k : ∀ t, F t.dmem → Keeps F (ret t)) :
    Keeps F (s.setAvxLegacy x v p ret align) := by
  cases x with
  | avx r => exact k _ hs
  | mem a => exact storeAvx stable hs _ _ _ _ k

theorem avxOperation [Labels] [address_size : AddressSize] (stable : StoreStable F) {w}
    (i : AvxOperation w) (p : Std.Rco Int64) (s : MachineData) (hs : F s.dmem)
    (next : MachineData → Effects) (hn : ∀ t, F t.dmem → Keeps F (next t)) :
    Keeps F (i.interp p s next) := by
  cases i with
  | vmovups dst src =>
    simp only [AvxOperation.interp]
    apply avxRegMem hs _ _ _ _
    intro v t ht
    exact setAvx stable ht _ _ _ _ _ hn
  | movups dst src | movaps dst src =>
    simp only [AvxOperation.interp]
    apply avxRegMem hs _ _ _ _
    intro v t ht
    exact setAvxLegacy stable ht _ _ _ _ _ hn
  | subps dst src | addps dst src =>
    simp only [AvxOperation.interp]
    apply avxRegMem hs _ _ _ _
    intro v t ht
    apply avxRegMem ht _ _ _ _
    intro u t ht
    exact setAvxLegacy stable ht _ _ _ _ _ hn

theorem instruction [Labels] (stable : StoreStable F)
    (i : Instr) (p : Std.Rco Int64) (s : MachineData) (hs : F s.dmem)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
    (hn : ∀ t, F t.dmem → Keeps F (next t))
    (hj : ∀ pc t, F t.dmem → Keeps F (jmp pc t)) :
    Keeps F (i.interp s p next jmp) := by
  cases i with
  | regular addr width op => exact operation (address_size := ⟨addr⟩) stable op p s hs next jmp hn hj
  | avx addr width op => exact avxOperation (address_size := ⟨addr⟩) stable op p s hs next hn

theorem all_and (e : Effects) (P Q : MachineState → Prop) :
    e.All P → e.All Q → e.All (fun t => P t ∧ Q t) := by
  induction e with
  | done s => exact And.intro
  | unimplemented _ => exact False.elim
  | gp_unaligned _ _ => exact False.elim
  | nonmem_load => exact False.elim
  | nonmem_store => exact False.elim
  | undefined k ih => exact fun hp hq v => ih v (hp v) (hq v)
  | require_read_access a w k ih => exact ih ()
  | require_write_access a w k ih => exact ih ()
  | require_exec_access p k ih => exact ih ()

theorem step [Labels] (stable : StoreStable F) (fetch : Int64 → Option Decoded)
    (s : MachineState) (post : MachineState → Prop) (hs : F s.data.dmem)
    (run : instructionStep fetch s post) :
    instructionStep fetch s (fun t => post t ∧ F t.data.dmem) := by
  unfold instructionStep at run ⊢
  cases fetched : fetch s.pc with
  | none => simp only [fetched] at run
  | some decoded =>
    simp only [fetched] at run ⊢
    obtain ⟨positive,run⟩ := run
    refine ⟨positive,all_and _ _ _ run ?_⟩
    have keep := instruction stable decoded.instruction ⟨s.pc,s.pc+.ofNat decoded.size⟩ s.data hs
      (fun d => .done ⟨d,s.pc+.ofNat decoded.size⟩) (fun pc d => .done ⟨d,pc⟩)
      (fun _ ht _ => ht) (fun _ _ ht _ => ht)
    exact keep (all_mono _ _ _ (fun _ _ => True.intro) run)

/-- Strengthen an existing whole execution, including contracted services,
by an invariant proved directly from the ISA. No additional contract. -/
theorem eventually [Labels] (stable : StoreStable F) (fetch : Int64 → Option Decoded)
    {s post} (run : Eventually (instructionStep fetch) post s) (hs : F s.data.dmem) :
    Eventually (instructionStep fetch) (fun t => post t ∧ F t.data.dmem) s := by
  induction run with
  | done s hp => exact .done _ ⟨hp,hs⟩
  | step s mid ht later ih =>
    exact .step s _ (step stable fetch s mid hs ht) (fun t h => ih t h.1 h.2)

theorem mapped_stable (base : DataMem) :
    StoreStable (fun m => ∀ a n, (base.loadInt a n).isSome=true → (m.loadInt a n).isSome=true) := by
  intro m address size value mapped a n old
  exact storeInt_defined m a address n size value (mapped a n old)

theorem eventually_mapped [Labels] (fetch : Int64 → Option Decoded) {s post}
    (run : Eventually (instructionStep fetch) post s) :
    Eventually (instructionStep fetch) (fun t => post t ∧
      ∀ a n, (s.data.dmem.loadInt a n).isSome=true → (t.data.dmem.loadInt a n).isSome=true) s :=
  eventually (mapped_stable s.data.dmem) fetch run (fun _ _ h => h)

#print axioms eventually_mapped
end Binary.MemoryInvariant
