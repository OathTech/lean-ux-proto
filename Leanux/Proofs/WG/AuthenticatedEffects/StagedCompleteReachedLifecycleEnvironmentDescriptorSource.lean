import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleEnvironmentFrames

/-! The original descriptor wrapper is factored into fixed, explicitly typed
source tails. Allocation, fd acquisition and fd repayment retain their order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment.Descriptor
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver Points

def socketResult (f : Fd) (body : PrefixM Event Int) : Bool → PrefixM Event Int
  | true => pure (-EBADF)
  | false => do
      let ret ← body
      liftPrefix (liftFS (fdput f))
      pure ret

def socket (fd : Nat) (body : PrefixM Event Int) : PrefixM Event Int := do
  let f ← liftPrefix (liftFS (fdget fd))
  socketResult f body f.file.isNone

def requestCallback (body : PrefixM Event Int) : PrefixM Event Int := do
  liftPrefix (skipCut allocCuts)
  let ret ← body
  liftPrefix (skipCut allocCuts)
  pure ret

def requestFinish (fd fid : Nat) (ret : Int) : PrefixM Event Int := do
  _ ← socket fd (pure 0)
  liftPrefix (liftFS (setFdtSlot fd none))
  liftPrefix (liftFS (setFdtOpen fd false))
  liftPrefix (modifyFiles fun fs=>{fs with nextFd:=fd})
  liftPrefix (liftFS (freeFile fid))
  pure ret

def requestInstall (fd fid : Nat) (body : PrefixM Event Int) : PrefixM Event Int := do
  liftPrefix (liftFS (setFile fid { fFlags:=O_RDWR, fMode:=FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED, fCount:=1, fOp:=some (.fixture "rtnetlink"), fInode:=some (.fixture "rtnetlink") }))
  liftPrefix (modify fun w=>{w with fs:={w.fs with nextFile:=fid+1}})
  liftPrefix (liftFS (setFdtSlot fd (some fid)))
  liftPrefix (liftFS (setFdtOpen fd true))
  liftPrefix (liftFS (setFdtCloexec fd false))
  let ret ← socket fd (requestCallback body)
  requestFinish fd fid ret

def limit : Bool → PrefixM Event Unit
  | true => liftPrefix (unsupported "no descriptor below RLIMIT_NOFILE for the temporary rtnetlink socket (the guest fails)")
  | false => pure ()

def requestChosen (fd : Nat) (body : PrefixM Event Int) : PrefixM Event Int := do
  let task ← liftPrefix (getTask .task)
  limit (decide (fd ≥ task.rlimitNofile))
  let saved ← liftPrefix (get : Leanux.M World)
  requestInstall fd saved.fs.nextFile body

def requestChoice (body : PrefixM Event Int) : Option Nat → PrefixM Event Int
  | none => liftPrefix (unsupported "no free descriptor in the table for the temporary rtnetlink socket (expansion)")
  | some fd => requestChosen fd body

def request (body : PrefixM Event Int) : PrefixM Event Int := do
  let fs ← liftPrefix getFiles
  requestChoice body ((List.range fs.fdt.maxFds).find? (fun n=>n≥fs.nextFd && !(fs.fdt.openFds.getD n true)))

theorem socket_source (fd : Nat) (body : PrefixM Event Int) :
    socketCallOnWith (fun {_} a=>liftPrefix a) fd body=socket fd body := by
  unfold socketCallOnWith socket
  apply congrArg (Bind.bind (liftPrefix (liftFS (fdget fd))))
  funext f
  cases branch : f.file.isNone <;> simp only [Bool.false_eq_true,ite_false,ite_true,socketResult]

theorem request_source (body : PrefixM Event Int) :
    rtnetlinkRequestWith (fun {_} a=>liftPrefix a) body=request body := by
  unfold rtnetlinkRequestWith request
  apply congrArg (Bind.bind (liftPrefix getFiles))
  funext fs
  dsimp only
  cases choice : (List.range fs.fdt.maxFds).find? (fun n=>n≥fs.nextFd && !(fs.fdt.openFds.getD n true)) with
  | none => rfl
  | some fd =>
    dsimp only [requestChoice,requestChosen]
    apply congrArg (Bind.bind (liftPrefix (getTask .task)))
    funext task
    by_cases exceeded : fd≥task.rlimitNofile <;>
      simp only [exceeded,ite_true,ite_false,decide_true,decide_false,limit,pure_bind,
        requestInstall,requestCallback,requestFinish,socket_source]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment.Descriptor
