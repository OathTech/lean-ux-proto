import Leanux.Kernel.Defs

/-!
# `struct kiocb` (include/linux/fs.h)

Shared by the eventfd and pipe `read_iter`/`write_iter` operations. (Moved
here from `Leanux.FS.EventfdOps` so that `Leanux.FS.Pipe`, which
`EventfdOps`'s `f_op` dispatch calls, can use it.)
-/

namespace Leanux

/-- `struct kiocb`, the parts the `read_iter`/`write_iter` operations consult. -/
structure Kiocb where
  filp : FileId
  kiFlags : UInt32
  kiPos : Int

/-- `IOCB_NOWAIT` (include/linux/fs.h). -/
def IOCB_NOWAIT : UInt32 := 0x8   -- RWF_NOWAIT

end Leanux
