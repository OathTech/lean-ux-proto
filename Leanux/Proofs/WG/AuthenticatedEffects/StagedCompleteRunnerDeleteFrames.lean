import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerCompanionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketEnvironmentChecked

/-! Deletion consumes its native entry companions at the actual guarded
destructor. The surrounding descriptor and syscall frames preserve that
entry until the callback, then preserve the resulting packet ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner.DeleteFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def Entry (h : List Event) (w : World) : Prop :=
  CompleteProduct.Carrier h w ∧ Companions w ∧ TxWork.Serving [] [] [] w.wg

theorem safe (h : List Event) (w : World) (before : Entry h w) : CompleteProduct.Safe h :=
  CompleteProduct.carrier_safe h w before.1

theorem store (h : List Event) (w v : World)
    (same : wgStoreView v.wg=wgStoreView w.wg) (before : Entry h w) : Entry h v :=
  ⟨CompleteProduct.store_transport h w v same before.1,before.2.1.store same,
    TxWork.serving_store_transport same before.2.2⟩

abbrev Keeps (body : PrefixM Event α) :=
  PrefixEnsures Entry CompleteProduct.Safe body (fun _=>Entry)
abbrev Checked (body : PrefixM Event α) :=
  PrefixEnsures Entry CompleteProduct.Safe body (fun _ => CompleteProduct.Carrier)

theorem weaken (before : Keeps body) : Checked body :=
  PrefixEnsures.consequence before (fun _ _ h => h) (fun _ _ _ h => h.1)

theorem native (body : Leanux.M α) (keeps : ∀ h, Preserves (Entry h) body) : Keeps (liftPrefix body) :=
  PrefixEnsures.lift body safe
    (fun h w value v hi run => (hoare_iff_run _ _ _).mp (keeps h) w value v hi run)

theorem fs (body : FS.M α) : Keeps (liftPrefix (liftFS body)) :=
  native _ (fun h => productFS_spec body _ (fun w _ _ _ hi => store h w _ rfl hi))

theorem seccomp (body : Seccomp.M α) : Keeps (liftPrefix (liftSeccomp body)) :=
  native _ (fun h => productSeccomp_spec body _ (fun w _ _ _ hi => store h w _ rfl hi))

theorem ambient (body : AmbientM α) : Keeps (liftPrefix (liftAmbient body)) :=
  native _ (fun h => productAmbient_spec body _ (fun w _ hi => store h w _ rfl hi))

theorem edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg=wgStoreView w.wg) :
    Keeps (liftPrefix (_root_.modify f : Leanux.M Unit)) :=
  native _ (fun h => hoare_modify _ (fun w hi => store h w (f w) (same w) hi))

theorem read : Keeps (liftPrefix (get : Leanux.M World)) :=
  native _ (fun _ => hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))

theorem read_files : Keeps (liftPrefix (getFiles : Leanux.M FilesStruct)) := by
  apply native
  intro h
  have taskFrame (a : TaskM Task) : Preserves (Entry h) (monadLift a : Leanux.M Task) :=
    productFS_spec (monadLift a : FS.M Task) _ (fun w _ _ _ hi => store h w _ rfl hi)
  routing_tx_source [getFiles,getTask] using [taskFrame]

theorem read_task (t : TaskRef) : Keeps (liftPrefix (getTask t : Leanux.M Task)) :=
  fs (monadLift (TaskM.getTask t) : FS.M Task)

theorem modify_files (f : FilesStruct → FilesStruct) :
    Keeps (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  fs (monadLift (TaskM.modifyTask .task (fun t => {t with files := f t.files})) : FS.M Unit)

theorem env_delete : Checked (Driver.envDeleteObserved hooks) := by
  intro w h before
  obtain ⟨history,cs,entry⟩ := before.2.1.1
  exact RetiredPeer.Lifecycle.Packet.Environment.checked w h
    ⟨before.1,entry.2,entry.1.1.2.1,before.2.1.2,before.2.2⟩

theorem socket (fd : Nat) (body : PrefixM Event Int) (checked : Checked body) :
    Checked (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply PrefixEnsures.bind (fs (fdget fd))
  intro f
  apply PrefixEnsures.ite
  · intro _; exact PrefixEnsures.pure safe (fun _ _ hi => hi.1)
  · intro _
    exact PrefixEnsures.bind checked (fun ret =>
      CompleteProduct.bind_checked (CompleteProduct.fs (fdput f))
        (fun _ => CompleteProduct.pure_checked ret))

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
  apply PrefixEnsures.bind read
  intro w
  apply PrefixEnsures.bind (fs (setFile w.fs.nextFile _))
  intro _
  apply PrefixEnsures.bind (edit (fun u=>{u with fs:={u.fs with nextFile:=w.fs.nextFile+1}}) (fun _=>rfl))
  intro _
  apply PrefixEnsures.bind (fs (setFdtSlot fd _))
  intro _
  apply PrefixEnsures.bind (fs (setFdtOpen fd true))
  intro _
  apply PrefixEnsures.bind (fs (setFdtCloexec fd false))
  intro _
  apply PrefixEnsures.bind (Q:=fun _=>CompleteProduct.Carrier)
  · apply socket
    exact PrefixEnsures.bind (ambient (AmbientM.skipCut allocCuts)) (fun _=>
      PrefixEnsures.bind checked (fun ret=>
        CompleteProduct.bind_checked (CompleteProduct.ambient (AmbientM.skipCut allocCuts))
          (fun _=>CompleteProduct.pure_checked ret)))
  intro ret
  change CompleteProduct.Checked _
  repeat' first
    | (complete_product_head socketCallOnWith; apply CompleteProduct.socket; change CompleteProduct.Checked _)
    | complete_outer_step

theorem rtnetlink (body : PrefixM Event Int) (checked : Checked body) :
    Checked (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  apply PrefixEnsures.bind read_files
  intro files
  dsimp only
  split
  · rename_i fd selected
    apply PrefixEnsures.bind (read_task .task)
    intro task
    apply PrefixEnsures.ite
    · intro _
      exact PrefixEnsures.bind (ambient (AmbientM.unsupported _))
        (fun _=>rtnetlink_body fd body checked)
    · intro _; exact rtnetlink_body fd body checked
  · exact weaken (ambient (AmbientM.unsupported _))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner.DeleteFrames
