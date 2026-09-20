import Leanux.FS.EventfdTypes

namespace Leanux.FS.Eventfd

/-- The output assignment in eventfd_ctx_do_read, including its zero case. -/
def readValue (ctx : Ctx) : UInt64 :=
  if ctx.semaphore && ctx.count != 0 then 1 else ctx.count

/-- The separate counter subtraction following the output assignment. -/
def eventfdCtxDoRead (ctx : Ctx) : ReadResult :=
  let value := readValue ctx
  { value, next := { ctx with count := ctx.count - value } }

structure Checked (α : Type) where
  result : Except Nat α
  branches : List String

/-- Supported caller has a valid buffer and a nonblocking file. -/
def eventfdRead (ctx : Ctx) (size : Nat) : Checked ReadResult :=
  if size < 8 then
    ⟨.error 22, ["eventfd_read.short_buffer"]⟩
  else if ctx.count == 0 then
    ⟨.error 11, ["eventfd_read.empty_nonblocking"]⟩
  else
    ⟨.ok (eventfdCtxDoRead ctx),
      ["eventfd_read.ready", if ctx.semaphore then "eventfd_ctx_do_read.semaphore"
        else "eventfd_ctx_do_read.ordinary", "eventfd_read.copy_success"]⟩

/-- The C unsigned subtraction guard prevents overflow and excludes UINT64_MAX. -/
def eventfdWrite (ctx : Ctx) (size : Nat) (value : UInt64) : Checked Ctx :=
  if size != 8 then
    ⟨.error 22, ["eventfd_write.wrong_size"]⟩
  else if value == 18446744073709551615 then
    ⟨.error 22, ["eventfd_write.reserved_value"]⟩
  else if (18446744073709551615 : UInt64) - ctx.count > value then
    ⟨.ok { ctx with count := ctx.count + value }, ["eventfd_write.add"]⟩
  else
    ⟨.error 11, ["eventfd_write.full_nonblocking"]⟩

end Leanux.FS.Eventfd
