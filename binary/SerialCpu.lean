import PeerScalars

namespace Binary

/-- In this one-CPU image, nr_cpumask_bits is 1. queueing.h reads the
    signed stored int into unsigned int before testing it. All bit patterns
    therefore have a representation, including high-bit values. -/
def decodeSerialCpu (raw : BitVec 32) : Option Nat :=
  if raw = 1 then none else some raw.toNat

/-- Functional decoding supplements the generated getD equation; no
    restriction is placed on the physical word. -/
def SerialCpuField (memory : Mem 64) (peer : BitVec 64) (cpu : Option Nat) : Prop :=
  ∃ raw : BitVec 32,
    memory.loadInt (peer + .ofNat 64 Layouts.peer_serial_work_cpu) 4 = some (raw.toNat : Int) ∧
    cpu = decodeSerialCpu raw

theorem decodeSerialCpu_getD (raw : BitVec 32) :
    (decodeSerialCpu raw).getD 1 = raw.toNat := by
  by_cases h : raw = 1
  · subst raw; rfl
  · simp only [decodeSerialCpu, if_neg h, Option.getD_some]

theorem SerialCpuField.of_word {memory peer} (raw : BitVec 32)
    (loaded : memory.loadInt (peer + .ofNat 64 Layouts.peer_serial_work_cpu) 4 = some (raw.toNat : Int)) :
    SerialCpuField memory peer (decodeSerialCpu raw) := ⟨raw, loaded, rfl⟩

theorem SerialCpuField.functional {memory peer a b}
    (ha : SerialCpuField memory peer a) (hb : SerialCpuField memory peer b) : a = b := by
  obtain ⟨wa, la, rfl⟩ := ha
  obtain ⟨wb, lb, rfl⟩ := hb
  have values := Option.some.inj (la.symm.trans lb)
  have words : wa = wb := BitVec.eq_of_toNat_eq (by omega)
  rw [words]

theorem SerialCpuField.generated {memory peer cpu}
    (h : SerialCpuField memory peer cpu) :
    memory.loadInt (peer + .ofNat 64 Layouts.peer_serial_work_cpu) 4 = some (cpu.getD 1 : Int) := by
  obtain ⟨raw, loaded, rfl⟩ := h
  simpa only [decodeSerialCpu_getD] using loaded

theorem SerialCpuField.frame {before after peer cpu writes}
    (same : EqualOutside writes before after)
    (apart : ∀ i < 4, ¬writes (peer + .ofNat 64 Layouts.peer_serial_work_cpu + .ofNat 64 i))
    (h : SerialCpuField before peer cpu) : SerialCpuField after peer cpu := by
  obtain ⟨raw, loaded, decoded⟩ := h
  exact ⟨raw, (same.loadInt _ 4 apart).symm.trans loaded, decoded⟩

#print axioms decodeSerialCpu_getD
#print axioms SerialCpuField.of_word
#print axioms SerialCpuField.functional
#print axioms SerialCpuField.generated
#print axioms SerialCpuField.frame
end Binary
