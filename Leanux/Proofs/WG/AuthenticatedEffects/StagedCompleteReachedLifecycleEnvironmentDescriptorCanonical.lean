import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleEnvironmentDescriptorFrames

/-! A fixed descriptor witness exposes all filesystem allocation/repayment
atoms and the original guarded callback. It is independent of any entry proof. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment.Descriptor
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver Points

noncomputable def socketResultShape (f : Fd) (body : Shape action) :
    (missing : Bool)→Shape (socketResult f action missing)
  | true => .pure _
  | false => .bind body (fun ret=>.bind (Atom.fs (fdput f)).shape (fun _=>.pure ret))

noncomputable def socketShape (fd : Nat) (body : Shape action) : Shape (socket fd action) :=
  .bind (Atom.fs (fdget fd)).shape (fun f=>socketResultShape f body f.file.isNone)

noncomputable def requestCallbackShape (body : Shape action) : Shape (requestCallback action) :=
  .bind (Atom.ambient (AmbientM.skipCut allocCuts)).shape (fun _=>.bind body (fun ret=>
    .bind (Atom.ambient (AmbientM.skipCut allocCuts)).shape (fun _=>.pure ret)))

noncomputable def requestFinishShape (fd fid : Nat) (ret : Int) : Shape (requestFinish fd fid ret) :=
  .bind (socketShape fd (.pure 0)) (fun _=>
    .bind (Atom.fs (setFdtSlot fd none)).shape (fun _=>
      .bind (Atom.fs (setFdtOpen fd false)).shape (fun _=>
        .bind (Atom.modifyFiles (fun fs=>{fs with nextFd:=fd})).shape (fun _=>
          .bind (Atom.fs (freeFile fid)).shape (fun _=>.pure ret)))))

noncomputable def requestInstallShape (fd fid : Nat) (body : Shape action) : Shape (requestInstall fd fid action) :=
  .bind (Atom.fs (setFile fid { fFlags:=O_RDWR, fMode:=FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED, fCount:=1, fOp:=some (.fixture "rtnetlink"), fInode:=some (.fixture "rtnetlink") })).shape (fun _=>
    .bind (Atom.nextFile (fid+1)).shape (fun _=>
      .bind (Atom.fs (setFdtSlot fd (some fid))).shape (fun _=>
        .bind (Atom.fs (setFdtOpen fd true)).shape (fun _=>
          .bind (Atom.fs (setFdtCloexec fd false)).shape (fun _=>
            .bind (socketShape fd (requestCallbackShape body)) (requestFinishShape fd fid))))))

noncomputable def limitShape : (exceeded : Bool)→Shape (limit exceeded)
  | true => (Atom.ambient (AmbientM.unsupported _)).shape
  | false => .pure ()

noncomputable def requestChosenShape (fd : Nat) (body : Shape action) : Shape (requestChosen fd action) :=
  .bind Atom.task.shape (fun task=>
    .bind (limitShape (decide (fd≥task.rlimitNofile))) (fun _=>
      .bind Atom.read.shape (fun saved=>requestInstallShape fd saved.fs.nextFile body)))

noncomputable def requestChoiceShape (body : Shape action) : (choice : Option Nat)→Shape (requestChoice action choice)
  | none => (Atom.ambient (AmbientM.unsupported _)).shape
  | some fd => requestChosenShape fd body

noncomputable def requestShape (body : Shape action) : Shape (request action) :=
  .bind Atom.files.shape (fun fs=>requestChoiceShape body
    ((List.range fs.fdt.maxFds).find? (fun n=>n≥fs.nextFd && !(fs.fdt.openFds.getD n true))))

noncomputable def originalSocket (fd : Nat) (body : Shape action) :
    Shape (socketCallOnWith (fun {_} a=>liftPrefix a) fd action) :=
  (congrArg Shape (socket_source fd action)).mpr (socketShape fd body)

noncomputable def originalRequest (body : Shape action) :
    Shape (rtnetlinkRequestWith (fun {_} a=>liftPrefix a) action) :=
  (congrArg Shape (request_source action)).mpr (requestShape body)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment.Descriptor
