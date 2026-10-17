import Leanux.Proofs.WG.Queues.JointSyscallSet

/-! The temporary rtnetlink descriptor is created, used and closed in one
execution. The shared source keeps allocation refusals, errno returns and
failed callback prefixes without assuming a valid fixture descriptor. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
universe u

def rtnetlinkRequestWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → Leanux.M α → m α) (handler : m Int) : m Int := do
  let fs ← lift getFiles
  let t := fs.fdt
  let some fd := (List.range t.maxFds).find? (fun n => n ≥ fs.nextFd && !(t.openFds.getD n true))
    | lift (unsupported "no free descriptor in the table for the temporary rtnetlink socket (expansion)")
  if fd ≥ (← lift (getTask .task)).rlimitNofile then
    lift (unsupported "no descriptor below RLIMIT_NOFILE for the temporary rtnetlink socket (the guest fails)")
  let fid := (← lift get).fs.nextFile
  lift (liftFS (setFile fid { fFlags := O_RDWR, fMode := FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED, fCount := 1, fOp := some (.fixture "rtnetlink"), fInode := some (.fixture "rtnetlink") }))
  lift (modify fun w => {w with fs := {w.fs with nextFile := fid + 1}})
  lift (liftFS (setFdtSlot fd (some fid)))
  lift (liftFS (setFdtOpen fd true))
  lift (liftFS (setFdtCloexec fd false))
  let ret ← socketCallOnWith lift fd do
    lift (skipCut allocCuts)
    let ret ← handler
    lift (skipCut allocCuts)
    pure ret
  _ ← socketCallOnWith lift fd (pure 0)
  lift (liftFS (setFdtSlot fd none))
  lift (liftFS (setFdtOpen fd false))
  lift (modifyFiles fun fs => {fs with nextFd := fd})
  lift (liftFS (freeFile fid))
  return ret

theorem rtnetlinkRequest_factor (body : Leanux.M Int) :
    Leanux.rtnetlinkRequest body = rtnetlinkRequestWith (fun {_} a => a) body := rfl

theorem rtnetlinkRequestObserved_factor (body : PrefixM AllowedIps.RoutingCompletion Int) :
    rtnetlinkRequestObserved body = rtnetlinkRequestWith (fun {_} a => liftPrefix a) body := rfl

theorem rtnetlinkRequestAudit_factor (body : AuditM Int) :
    rtnetlinkRequestAudit body = rtnetlinkRequestWith (fun {_} a => liftPrefix a) body := rfl

theorem rtnetlinkRequestWith_projects {E F : Type} (ρ : E → Option F)
    {body : PrefixM E Int} {lower : PrefixM F Int} (hb : ProjectsPrefix ρ id body lower) :
    ProjectsPrefix ρ id (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body)
      (rtnetlinkRequestWith (fun {_} a => liftPrefix a) lower) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | with_reducible exact hb
    | with_reducible exact projectsPrefix_lift ρ _
    | with_reducible exact projectsPrefix_pure ρ id _
    | with_reducible apply socketCallOnWith_projects ρ
    | with_reducible apply projectsPrefix_bind ρ id id
    | (maintenance_intro; try dsimp only [id])
    | (split <;> try contradiction)
  all_goals exact fun _ _ => rfl

theorem rtnetlinkRequestWith_appends {E : Type} {body : PrefixM E Int}
    (hb : Appends body) : Appends (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | with_reducible exact hb
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply socketCallOnWith_appends
    | with_reducible apply Appends.bind
    | (maintenance_intro; try dsimp only)
    | split

theorem rtnetlinkRequestWith_focuses {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e)
    {body : PrefixM F Int} {lower : PrefixM E Int}
    (hb : FocusesUnder (fun _ _ => True) encode decode body lower) (hl : Appends lower) :
    FocusesUnder (fun _ _ => True) encode decode
      (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body)
      (rtnetlinkRequestWith (fun {_} a => liftPrefix a) lower) := by
  have preserve {G α : Type} {a : PrefixM G α} (ha : Appends a) :
      PrefixPreserves (fun _ _ => True) (fun _ => True) a :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointNetlink.«0».Leanux.Proofs.WG.Configuration.true_preserves) ha
  unfold rtnetlinkRequestWith
  repeat' first
    | with_reducible exact hb
    | with_reducible exact FocusesUnder.lift _
    | with_reducible exact FocusesUnder.pure _
    | with_reducible apply socketCallOnWith_focuses encode decode hd
    | with_reducible apply FocusesUnder.bind hd
    | with_reducible apply preserve
    | with_reducible exact hl
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply socketCallOnWith_appends
    | with_reducible apply Appends.bind
    | (maintenance_intro; try dsimp only)
    | split

theorem rtnetlinkRequestWith_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e) (body : PrefixM E Int) (hb : Appends body) :
    rtnetlinkRequestWith (fun {_} a => liftPrefix a) (focusPrefix encode decode body) =
      focusPrefix encode decode (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  funext w h
  exact rtnetlinkRequestWith_focuses encode decode hd (FocusesUnder.focus body) hb w h True.intro

end Leanux.Proofs.WG.Configuration

namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Configuration AllowedIps

def dispatchCreate : PrefixM Event Int :=
  rtnetlinkRequestWith (fun {_} a => liftPrefix a)
    (rxAction (RxHistory.mixed (liftWGObserver wgCreatePrefix)))

theorem dispatchCreate_routing : ProjectsPrefix routingEvent id dispatchCreate (dispatchObserved .wgCreate) := by
  change ProjectsPrefix routingEvent id dispatchCreate (rtnetlinkRequestObserved (liftPrefix (liftWG wgCreate)))
  rw [rtnetlinkRequestObserved_factor]
  exact rtnetlinkRequestWith_projects routingEvent
    (rxAction_routing (RxHistory.mixed_erases (liftWGObserver_erases wgCreatePrefix_erases)))

theorem dispatchCreate_rx : ProjectsPrefix rxEvent id dispatchCreate (RxHistory.syscallDispatch .wgCreate) := by
  change ProjectsPrefix rxEvent id dispatchCreate
    (RxHistory.audit (rtnetlinkRequestAudit (auditFocus (liftWGObserver wgCreatePrefix))))
  rw [rtnetlinkRequestAudit_factor]
  unfold RxHistory.audit
  rw [← rtnetlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (auditFocus (liftWGObserver wgCreatePrefix)) (Appends.focus _ _ _)]
  exact rtnetlinkRequestWith_projects rxEvent (rxAction_rx (Appends.focus _ _ _))

theorem dispatchCreate_erases : ErasesPrefix dispatchCreate (Leanux.dispatch .wgCreate) := by
  intro w h
  have hp := congrArg Prod.fst (dispatchCreate_rx w h)
  have he := RxHistory.syscallDispatch_erases .wgCreate w (h.filterMap rxEvent)
  have same := hp.symm.trans he
  change ((runPrefix dispatchCreate w h).1.map (fun (x,v) => (x,v))) = _ at same
  cases hr : (runPrefix dispatchCreate w h).1 <;> simpa only [hr,Except.map] using same

end Leanux.Proofs.WG.Queues.RoutingJoint
