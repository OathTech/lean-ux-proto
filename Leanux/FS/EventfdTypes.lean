import Std

namespace Leanux.FS.Eventfd

/-- Frozen mirror interface for the local counter computation. -/
structure Ctx where
  count : UInt64
  semaphore : Bool
  deriving Repr, BEq, DecidableEq

structure ReadResult where
  value : UInt64
  next : Ctx
  deriving Repr, BEq, DecidableEq

end Leanux.FS.Eventfd
