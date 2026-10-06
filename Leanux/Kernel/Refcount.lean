import Leanux.Kernel.Defs

/-! include/linux/refcount.h helpers shared by kref users. -/

namespace Leanux

/-- `refcount_dec_and_test` = `__refcount_sub_and_test(1, r, NULL)`
    (include/linux/refcount.h:262-278). `if (oldp)` is constant-folded away
    (NULL); saturation reports are `unsupported`. -/
def refcountDecAndTest (old : Nat) : M Bool := do
  let i := 1
  if ← branchCmp .refcountSubPositive (old > 0) old 0 then
    if ← branchCmp .refcountSubToZero (old == i) old i then return true
  if ← branch .refcountSubNonpositive (old == 0) then unsupported "refcount_warn_saturate (use after free)"
  if ← branch .refcountSubUnderflow (old < i) then unsupported "refcount_warn_saturate (underflow)"
  return false

/-- `refcount_inc` = `__refcount_add(1, r, NULL)` (include/linux/refcount.h:182-193). -/
def refcountInc (old : Nat) : M Unit := do
  -- `if (oldp)` is constant-folded away (NULL)
  if ← branchCmp .refcountAddFromZero (old == 0) old 0 then
    unsupported "refcount_warn_saturate (add on zero)"
  -- `old < 0 || old + i < 0`
  if ← branch .refcountAddNegative false then unsupported "unreachable"
  if ← branch .refcountAddWraps (old + 1 ≥ 2 ^ 31) then
    unsupported "refcount_warn_saturate (overflow)"

/-- `refcount_inc` on a guest-wide count the mirror does not model, at a
    declared operand exclusion (`x`): the same decisions as `refcountInc`,
    with the outcomes the contract fixes (a live object: not zero, no
    overflow) and `__refcount_add.old_zero` reported without operands. -/
def refcountIncGuestWide (x : OperandExclusion) : M Unit := do
  if ← branchCmpExcluded .refcountAddFromZero false x then
    unsupported "refcount_warn_saturate (add on zero)"
  if ← branch .refcountAddNegative false then unsupported "unreachable"
  if ← branch .refcountAddWraps false then unsupported "refcount_warn_saturate (overflow)"

/-- `kref_get_unless_zero` = `__refcount_add_not_zero(1, r, NULL)`
    (include/linux/refcount.h:139-156). Single-threaded, so the cmpxchg
    succeeds at once. Returns whether the count was nonzero. -/
def refcountIncNotZero (old : Nat) : M Bool := do
  if !(← branchCmp .refcountAddNzZero (old == 0) old 0) then
    _ ← branch .refcountAddNzRetry false
  if ← branch .refcountAddNzNegative false then unsupported "unreachable"
  if ← branch .refcountAddNzWraps (old + 1 ≥ 2 ^ 31) then
    unsupported "refcount_warn_saturate (overflow)"
  return old != 0

end Leanux
