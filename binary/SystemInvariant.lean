import Execution
import Memory

namespace Binary.SystemInvariant

/-- The ISA may update IF; other system-state properties are carried
through actual instruction execution, including contracted service bodies. -/
def IFStable (F : SystemFlags → Prop) : Prop :=
  ∀ flags enabled, F flags → F (flags.setIF enabled)

def Keeps (F : SystemFlags → Prop) (e : Effects) : Prop :=
  e.All (fun _ => True) → e.All (fun t => F t.data.system)

variable {F : SystemFlags → Prop}

theorem load {s : MachineData} (hs : F s.system) (a w ret)
    (k : ∀ v t, F t.system → Keeps F (ret v t)) : Keeps F (s.load a w ret) := by
  unfold MachineData.load Keeps
  simp only [Effects.All]
  split
  · exact k _ _ hs
  · exact False.elim

theorem store {s : MachineData} (hs : F s.system)
    (a) {w : Width} (v : w.type) (ret) (k : ∀ t, F t.system → Keeps F (ret t)) :
    Keeps F (s.store a v ret) := by
  unfold MachineData.store Keeps
  simp only [Effects.All]
  split
  · exact k _ hs
  · exact False.elim

theorem regMem [Labels] [AddressSize] {s : MachineData} (hs : F s.system)
    {w} (x : RegOrMem w) (p ret) (k : ∀ v t, F t.system → Keeps F (ret v t)) :
    Keeps F (x.interp s p ret) := by
  cases x with
  | reg r => exact k _ _ hs
  | mem a => exact load hs _ _ _ k

theorem reg {s : MachineData} (hs : F s.system) {w} (x : Reg w) (p ret)
    (k : ∀ v t, F t.system → Keeps F (ret v t)) : Keeps F (x.interp s p ret) := k _ _ hs

theorem operand [Labels] [AddressSize] {s : MachineData} (hs : F s.system)
    {w} (x : Operand w) (p ret) (k : ∀ v t, F t.system → Keeps F (ret v t)) :
    Keeps F (x.interp s p ret) := by
  cases x with
  | regOrMem x => exact regMem hs _ _ _ k
  | imm x => exact k _ _ hs

theorem relative [Labels] [AddressSize] {s : MachineData} (hs : F s.system)
    (x : RelRegOrMem) (p ret) (k : ∀ v t, F t.system → Keeps F (ret v t)) :
    Keeps F (x.interp s p ret) := by
  cases x with
  | rel x => exact k _ _ hs
  | reg x => exact k _ _ hs
  | mem a => exact load hs _ _ _ k

theorem set [Labels] [AddressSize] {s : MachineData} (hs : F s.system)
    {w} (x : Dst w) (v p ret) (k : ∀ t, F t.system → Keeps F (ret t)) :
    Keeps F (s.set x v p ret) := by
  cases x with
  | reg r => exact k _ hs
  | mem a => exact store hs _ _ _ k

theorem undefined {α} [NondetSupportingType α] {k : α → Effects}
    (h : ∀ v, Keeps F (k v)) : Keeps F (.undefined k) := by
  intro success v
  exact h v (success v)

theorem impossible (s : String) : Keeps F (.unimplemented s) := False.elim

theorem stosOne (w : Width) {s : MachineData}
    (hs : F s.system) (next : MachineData → Effects)
    (hn : ∀ t, F t.system → Keeps F (next t)) : Keeps F (s.stosOne w next) := by
  unfold MachineData.stosOne
  apply store hs
  intro t ht
  exact hn _ ht

theorem stosRepeat (w : Width) (count : Nat)
    (s : MachineData) (hs : F s.system) (next : MachineData → Effects)
    (hn : ∀ t, F t.system → Keeps F (next t)) :
    Keeps F (MachineData.stosRepeat w count s next) := by
  induction count generalizing s with
  | zero => exact hn _ hs
  | succ count ih =>
    unfold MachineData.stosRepeat
    apply stosOne w hs
    intro t ht
    exact ih _ ht

theorem movsOne (w : Width) {s : MachineData}
    (hs : F s.system) (next : MachineData → Effects)
    (hn : ∀ t, F t.system → Keeps F (next t)) : Keeps F (s.movsOne w next) := by
  unfold MachineData.movsOne
  apply load hs
  intro value t ht
  apply store ht
  intro t ht
  exact hn _ ht

theorem movsRepeat (w : Width) (count : Nat)
    (s : MachineData) (hs : F s.system) (next : MachineData → Effects)
    (hn : ∀ t, F t.system → Keeps F (next t)) :
    Keeps F (MachineData.movsRepeat w count s next) := by
  induction count generalizing s with
  | zero => exact hn _ hs
  | succ count ih =>
    unfold MachineData.movsRepeat
    apply movsOne w hs
    intro t ht
    exact ih _ ht

/-- Follow the interpreter's state updates without simplifying arithmetic.
All branches and undefined choices are retained. -/
theorem operation [Labels] [address_size : AddressSize] (stable : IFStable F) {w}
    (i : Operation w) (p : Std.Rco Int64) (s : MachineData) (hs : F s.system)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
    (hn : ∀ t, F t.system → Keeps F (next t))
    (hj : ∀ pc t, F t.system → Keeps F (jmp pc t)) :
    Keeps F (i.interp p s next jmp) := by
  cases i
  case' cmpxchg dst _ => cases dst
  case' xadd dst _ => cases dst
  all_goals simp only [Operation.interp]
  case cli =>
    split
    · exact hn _ (stable _ false hs)
    · exact impossible _
  case sti =>
    split
    · exact hn _ (stable _ true hs)
    · exact impossible _
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
    | apply set (by assumption); intro t ht
    | apply store (by assumption); intro t ht
    | apply stosOne _ (by assumption); intro t ht
    | apply stosRepeat _ _ _ (by assumption); intro t ht
    | apply movsRepeat _ _ _ (by assumption); intro t ht
    | apply movsOne _ (by assumption); intro t ht
    | apply undefined; intro v
    | exact impossible _
    | exact hn _ (by assumption)
    | exact hj _ _ (by assumption)
    | split

#print axioms operation

theorem loadAvx {s : MachineData} (hs : F s.system) (a w ret align)
    (k : ∀ v t, F t.system → Keeps F (ret v t)) : Keeps F (s.loadAvx a w ret align) := by
  unfold MachineData.loadAvx Keeps
  split
  · exact False.elim
  · simp only [Effects.All]
    split
    · exact k _ _ hs
    · exact False.elim

theorem storeAvx {s : MachineData} (hs : F s.system)
    (a) {w : AvxWidth} (v : w.type) (ret align) (k : ∀ t, F t.system → Keeps F (ret t)) :
    Keeps F (s.storeAvx a v ret align) := by
  unfold MachineData.storeAvx Keeps
  split
  · exact False.elim
  · simp only [Effects.All]
    split
    · exact k _ hs
    · exact False.elim

theorem avxRegMem [Labels] [AddressSize] {s : MachineData} (hs : F s.system)
    {w} (x : AvxRegOrMem w) (p ret align) (k : ∀ v t, F t.system → Keeps F (ret v t)) :
    Keeps F (x.interp s p ret align) := by
  cases x with
  | avx r => exact k _ _ hs
  | mem a => exact loadAvx hs _ _ _ _ k

theorem avxOperand [Labels] [AddressSize] {s : MachineData} (hs : F s.system)
    {w} (x : AvxOperand w) (p ret align) (k : ∀ v t, F t.system → Keeps F (ret v t)) :
    Keeps F (x.interp s p ret align) := by
  cases x with
  | regOrMem x => exact avxRegMem hs _ _ _ _ k

theorem setAvx [Labels] [AddressSize] {s : MachineData} (hs : F s.system)
    {w} (x : AvxDst w) (v p ret align) (k : ∀ t, F t.system → Keeps F (ret t)) :
    Keeps F (s.setAvx x v p ret align) := by
  cases x with
  | avx r => exact k _ hs
  | mem a => exact storeAvx hs _ _ _ _ k

theorem setAvxLegacy [Labels] [AddressSize] {s : MachineData} (hs : F s.system)
    {w} (x : AvxDst w) (v p ret align) (k : ∀ t, F t.system → Keeps F (ret t)) :
    Keeps F (s.setAvxLegacy x v p ret align) := by
  cases x with
  | avx r => exact k _ hs
  | mem a => exact storeAvx hs _ _ _ _ k

theorem avxOperation [Labels] [address_size : AddressSize] {w}
    (i : AvxOperation w) (p : Std.Rco Int64) (s : MachineData) (hs : F s.system)
    (next : MachineData → Effects) (hn : ∀ t, F t.system → Keeps F (next t)) :
    Keeps F (i.interp p s next) := by
  cases i with
  | vmovups dst src =>
    simp only [AvxOperation.interp]
    apply avxRegMem hs _ _ _ _
    intro v t ht
    exact setAvx ht _ _ _ _ _ hn
  | movups dst src | movaps dst src =>
    simp only [AvxOperation.interp]
    apply avxRegMem hs _ _ _ _
    intro v t ht
    exact setAvxLegacy ht _ _ _ _ _ hn
  | subps dst src | addps dst src =>
    simp only [AvxOperation.interp]
    apply avxRegMem hs _ _ _ _
    intro v t ht
    apply avxRegMem ht _ _ _ _
    intro u t ht
    exact setAvxLegacy ht _ _ _ _ _ hn

theorem instruction [Labels] (stable : IFStable F)
    (i : Instr) (p : Std.Rco Int64) (s : MachineData) (hs : F s.system)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
    (hn : ∀ t, F t.system → Keeps F (next t))
    (hj : ∀ pc t, F t.system → Keeps F (jmp pc t)) :
    Keeps F (i.interp s p next jmp) := by
  cases i with
  | regular addr width op => exact operation (address_size := ⟨addr⟩) stable op p s hs next jmp hn hj
  | avx addr width op => exact avxOperation (address_size := ⟨addr⟩) op p s hs next hn

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

theorem step [Labels] (stable : IFStable F) (fetch : Int64 → Option Decoded)
    (s : MachineState) (post : MachineState → Prop) (hs : F s.data.system)
    (run : instructionStep fetch s post) :
    instructionStep fetch s (fun t => post t ∧ F t.data.system) := by
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
theorem eventually [Labels] (stable : IFStable F) (fetch : Int64 → Option Decoded)
    {s post} (run : Eventually (instructionStep fetch) post s) (hs : F s.data.system) :
    Eventually (instructionStep fetch) (fun t => post t ∧ F t.data.system) s := by
  induction run with
  | done s hp => exact .done _ ⟨hp,hs⟩
  | step s mid ht later ih =>
    exact .step s _ (step stable fetch s mid hs ht) (fun t h => ih t h.1 h.2)

/-- CPL and DF are invariant even through CLI/STI and arbitrary repeated
stores. This is proved from the interpreter, not a service assumption. -/
theorem eventually_mode [Labels] (fetch : Int64 → Option Decoded) {s post}
    (run : Eventually (instructionStep fetch) post s) :
    Eventually (instructionStep fetch) (fun t => post t ∧
      t.data.system.cpl=s.data.system.cpl ∧ t.data.system.bits[10]=s.data.system.bits[10]) s := by
  apply eventually (F := fun flags => flags.cpl=s.data.system.cpl ∧ flags.bits[10]=s.data.system.bits[10])
    (fun flags enabled prior => ?_) fetch run ⟨rfl,rfl⟩
  cases enabled <;> simpa [SystemFlags.setIF] using prior

#print axioms eventually_mode
end Binary.SystemInvariant
