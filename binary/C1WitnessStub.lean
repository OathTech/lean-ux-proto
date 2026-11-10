import C1ServiceCallbackPremises

/-! Result C1, open proposition `WitnessHolds`: the active stub.

Package 4's stub (`C1ServiceStub`) is quiet: it does not use its stack and
does not write the coverage buffer. This one puts three instructions in
front of the same body: it saves `rdi` on its stack, calls the image's own
`__sanitizer_cov_trace_pc` (whose behaviour is the landed contract, proved
from the image), and restores `rdi`. So it changes two words of its stack
scratch on every call, and it appends a record to the coverage buffer
whenever the buffer is in use and has room. The allocator's state, its
arena and `Idle` are package 4's, unchanged; the scratch is 16 bytes. -/
namespace Binary.Statements.C1.Witness
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.Statements.C1.Proof
open Kraken.X64.Parser
local instance : Labels := Image.linkedLabels

/-- `kmem_cache_alloc_noprof` as an active stub: save the cache pointer, call
the coverage callback, restore the pointer, then package 4's body (read the
count, advance it, read the pending outcome; on 1 return object `count`,
otherwise NULL). -/
def allocCode : List (Kraken.Sized Directive) :=
  List.zipWith (fun d n => ⟨d, n⟩) (parse("push   %rdi
call L_ffffffff810f31f0
pop    %rdi
movzbl (%rdi),%ecx
lea    0x1(%rcx),%eax
mov    %al,(%rdi)
movzbl 0xa00100(%rcx),%edx
cmp    $0x1,%edx
jne L_ffffffff81196d54
lea    0x0(,%rcx,8),%rcx
lea    0x0(,%rcx,8),%rcx
lea    0xa01000(,%rcx,2),%rax
ret
xor    %eax,%eax
ret")) [1, 5, 1, 3, 3, 2, 7, 3, 2, 8, 8, 8, 1, 2, 1]

/-- The stub's decoder: the active allocation code, and package 4's `ret` at `freeEntry`. -/
def fetch (pc : Int64) : Option Decoded :=
  (Image.fetchIn allocEntry allocCode pc).orElse fun _ => Image.fetchIn freeEntry Stub.freeCode pc

/-- Package 4's allocator state with a 16-byte scratch: the saved `rdi` and
the callback's return word. -/
def allocator : Allocator := ⟨Stub.Idle,16⟩

/-- The stub's code lies in the stub's interval. -/
theorem within : Joint.Within fetch Joint.stubLow Joint.stubHigh := by
  intro pc decoded here
  unfold fetch at here
  cases first : Image.fetchIn allocEntry allocCode pc with
  | some found =>
    have range := Callback.Text.fetchIn_address first (by decide +kernel)
    have low : Joint.stubLow ≤ allocEntry.toBitVec.toNat := by decide +kernel
    have high : allocEntry.toBitVec.toNat + Callback.Text.extent allocCode ≤ Joint.stubHigh := by
      decide +kernel
    omega
  | none =>
    rw [first] at here
    have range := Callback.Text.fetchIn_address (show Image.fetchIn freeEntry Stub.freeCode pc =
      some decoded from here) (by decide +kernel)
    have low : Joint.stubLow ≤ freeEntry.toBitVec.toNat := by decide +kernel
    have high : freeEntry.toBitVec.toNat + Callback.Text.extent Stub.freeCode ≤ Joint.stubHigh := by
      decide +kernel
    omega

#print axioms within
end Binary.Statements.C1.Witness
