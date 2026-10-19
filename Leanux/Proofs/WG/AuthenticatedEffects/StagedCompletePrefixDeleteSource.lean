import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDeleteFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixEnvironmentDelete

/-! Deletion's descriptor wrappers retain all prefixes before and after
the callback which consumes its stronger native entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner.Delete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal

theorem env_delete : Checked (Driver.envDeleteObserved hooks) := by
  intro w h before
  obtain ⟨history,cs,entry⟩ := before.1.2.1.1
  exact EnvironmentDelete.concrete w h
    ⟨⟨before.1.1,entry.2,entry.1.1.2.1,before.1.2.1.2,before.1.2.2⟩,before.2⟩

theorem socket (fd : Nat) (body : PrefixM Event Int) (checked : Checked body) :
    Checked (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply Ensures.bind (fs (fdget fd))
  intro f
  apply PrefixEnsures.ite
  · intro _; exact PrefixEnsures.pure (fun _ _ before=>before.2)
      (fun _ _ before=>⟨before.1.1,before.2⟩)
  · intro _
    exact Ensures.bind checked (fun ret =>
      Product.bind_checked (Product.fs (fdput f))
        (fun _ => Product.pure_checked ret))

theorem rtnetlink_body (fd : Nat) (body : PrefixM Event Int) (checked : Checked body) :
    Checked (do
      let w ← liftPrefix (get : Leanux.M World)
      let fid := w.fs.nextFile
      liftPrefix (liftFS (setFile fid { fFlags := O_RDWR, fMode := FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED, fCount := 1, fOp := some (.fixture "rtnetlink"), fInode := some (.fixture "rtnetlink") }))
      liftPrefix (modify fun w => {w with fs:={w.fs with nextFile:=fid+1}})
      liftPrefix (liftFS (setFdtSlot fd (some fid)))
      liftPrefix (liftFS (setFdtOpen fd true))
      liftPrefix (liftFS (setFdtCloexec fd false))
      let ret ← socketCallOnWith (fun {_} a=>liftPrefix a) fd do
        liftPrefix (skipCut allocCuts)
        let ret ← body
        liftPrefix (skipCut allocCuts)
        pure ret
      _ ← socketCallOnWith (fun {_} a=>liftPrefix a) fd (pure 0)
      liftPrefix (liftFS (setFdtSlot fd none))
      liftPrefix (liftFS (setFdtOpen fd false))
      liftPrefix (modifyFiles fun fs=>{fs with nextFd:=fd})
      liftPrefix (liftFS (freeFile fid))
      pure ret) := by
  apply Ensures.bind read
  intro w
  apply Ensures.bind (fs (setFile w.fs.nextFile _))
  intro _
  apply Ensures.bind (edit (fun u=>{u with fs:={u.fs with nextFile:=w.fs.nextFile+1}}) (fun _=>rfl))
  intro _
  apply Ensures.bind (fs (setFdtSlot fd _))
  intro _
  apply Ensures.bind (fs (setFdtOpen fd true))
  intro _
  apply Ensures.bind (fs (setFdtCloexec fd false))
  intro _
  apply Ensures.bind (Q:=fun _=>CompleteProduct.Carrier)
  · apply socket
    exact Ensures.bind (ambient (AmbientM.skipCut allocCuts)) (fun _=>
      Ensures.bind checked (fun ret=>
        Product.bind_checked (Product.ambient (AmbientM.skipCut allocCuts))
          (fun _=>Product.pure_checked ret)))
  intro ret
  change Product.Checked _
  repeat' first
    | (prefix_product_head socketCallOnWith; apply Product.socket; change Product.Checked _)
    | prefix_outer_step

theorem rtnetlink (body : PrefixM Event Int) (checked : Checked body) :
    Checked (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  apply Ensures.bind read_files
  intro files
  dsimp only
  split
  · rename_i fd selected
    apply Ensures.bind (read_task .task)
    intro task
    apply PrefixEnsures.ite
    · intro _
      exact Ensures.bind (ambient (AmbientM.unsupported _))
        (fun _=>rtnetlink_body fd body checked)
    · intro _; exact rtnetlink_body fd body checked
  · exact weaken (ambient (AmbientM.unsupported _))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner.Delete
