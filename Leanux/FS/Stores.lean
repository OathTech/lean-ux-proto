import Leanux.Kernel.Defs

/-! # The file layer's stores (the state split, phase 2)

The object stores of `FSWorld` with their lifetime-identity accessors, over
`FS.M` (docs/2026-10-15-design-state-split.md, sections 2 and 3): the files,
eventfd contexts, pipefs inodes, pipes, pages and the epoll stores, and the
bounds-checked descriptor-table access (the table itself is the task's,
reached through `TaskM`'s `getFiles`/`modifyFdt`). Moved from
`Kernel/Defs.lean` unchanged but for the monad. -/

namespace Leanux

def getFile (id : FileId) : FS.M File := do
  match (← get).files.get? id with
  | some f => return f
  | none => invariant s!"dangling file identity {id}"

def setFile (id : FileId) (f : File) : FS.M Unit :=
  modify fun k => { k with files := k.files.insert id f }

def freeFile (id : FileId) : FS.M Unit :=
  modify fun k => { k with files := k.files.erase id }

def getCtx (id : CtxId) : FS.M EventfdCtx := do
  match (← get).ctxs.get? id with
  | some c => return c
  | none => invariant s!"dangling eventfd context {id}"

def setCtx (id : CtxId) (c : EventfdCtx) : FS.M Unit :=
  modify fun k => { k with ctxs := k.ctxs.insert id c }

def freeCtx (id : CtxId) : FS.M Unit :=
  modify fun k => { k with ctxs := k.ctxs.erase id }

def getInode (id : PipefsInodeId) : FS.M Inode := do
  match (← get).inodes.get? id with
  | some i => return i
  | none => invariant s!"dangling pipefs inode identity {id}"

def setInode (id : PipefsInodeId) (i : Inode) : FS.M Unit :=
  modify fun k => { k with inodes := k.inodes.insert id i }

def getPipe (id : PipeId) : FS.M PipeInodeInfo := do
  match (← get).pipes.get? id with
  | some p => return p
  | none => invariant s!"dangling pipe identity {id}"

def setPipe (id : PipeId) (p : PipeInodeInfo) : FS.M Unit :=
  modify fun k => { k with pipes := k.pipes.insert id p }

def getPage (id : PageId) : FS.M Page := do
  match (← get).pages.get? id with
  | some p => return p
  | none => invariant s!"dangling page identity {id}"

def setPage (id : PageId) (p : Page) : FS.M Unit :=
  modify fun k => { k with pages := k.pages.insert id p }

/-! ## epoll stores (lifetime identities) -/

def getEp (id : EpId) : FS.M Eventpoll := do
  match (← get).eps.get? id with
  | some e => return e
  | none => invariant s!"dangling eventpoll identity {id}"

def setEp (id : EpId) (e : Eventpoll) : FS.M Unit :=
  modify fun k => { k with eps := k.eps.insert id e }

def freeEp (id : EpId) : FS.M Unit :=
  modify fun k => { k with eps := k.eps.erase id }

def getEpi (id : EpiId) : FS.M Epitem := do
  match (← get).epis.get? id with
  | some e => return e
  | none => invariant s!"dangling epitem identity {id}"

def setEpi (id : EpiId) (e : Epitem) : FS.M Unit :=
  modify fun k => { k with epis := k.epis.insert id e }

def freeEpi (id : EpiId) : FS.M Unit :=
  modify fun k => { k with epis := k.epis.erase id }

def getPwq (id : PwqId) : FS.M EppollEntry := do
  match (← get).pwqs.get? id with
  | some p => return p
  | none => invariant s!"dangling eppoll_entry identity {id}"

def setPwq (id : PwqId) (p : EppollEntry) : FS.M Unit :=
  modify fun k => { k with pwqs := k.pwqs.insert id p }

def freePwq (id : PwqId) : FS.M Unit :=
  modify fun k => { k with pwqs := k.pwqs.erase id }

/-! ## Bounds-checked descriptor-table access -/

private def at? (a : Array α) (n : Nat) (what : String) : FS.M α :=
  match a[n]? with
  | some x => return x
  | none => invariant s!"{what}[{n}] beyond max_fds"

/-- `fdt->fd[n]`. -/
def fdtSlot (fdt : Fdtable) (n : Nat) : FS.M (Option FileId) := at? fdt.fd n "fdt->fd"
/-- `test_bit(n, fdt->open_fds)`. -/
def fdtOpen (fdt : Fdtable) (n : Nat) : FS.M Bool := at? fdt.openFds n "fdt->open_fds"
/-- `test_bit(n, fdt->close_on_exec)`. -/
def fdtCloexec (fdt : Fdtable) (n : Nat) : FS.M Bool := at? fdt.closeOnExec n "fdt->close_on_exec"

private def setAt (a : Array α) (n : Nat) (x : α) (what : String) : FS.M (Array α) :=
  if n < a.size then return a.set! n x else invariant s!"{what}[{n}] beyond max_fds"

def setFdtSlot (n : Nat) (v : Option FileId) : FS.M Unit := do
  let t := (← getFiles).fdt
  let fd ← setAt t.fd n v "fdt->fd"
  modifyFdt fun t => { t with fd }
def setFdtOpen (n : Nat) (b : Bool) : FS.M Unit := do
  let t := (← getFiles).fdt
  let openFds ← setAt t.openFds n b "fdt->open_fds"
  modifyFdt fun t => { t with openFds }
def setFdtCloexec (n : Nat) (b : Bool) : FS.M Unit := do
  let t := (← getFiles).fdt
  let closeOnExec ← setAt t.closeOnExec n b "fdt->close_on_exec"
  modifyFdt fun t => { t with closeOnExec }

end Leanux
