import Leanux.Proofs.WG.Queues.JointDevice
import Leanux.Proofs.WG.Configuration.SyscallCompletion
import Leanux.Proofs.WG.Queues.RxSyscallDispatchHistory
import Leanux.Proofs.Logged.FocusComposition

/-! The product socket boundary shares one execution of the joint configuration
observer. Descriptor references, allocation cuts and acknowledgement handling
follow the original source for normal errors as well as successful returns. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
universe u

def socketCallOnWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → Leanux.M α → m α) (fd : Nat) (body : m Int) : m Int := do
  let f ← lift (liftFS (fdget fd))
  if f.file.isNone then return -EBADF
  let ret ← body
  lift (liftFS (fdput f))
  return ret

def netlinkRequestWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → Leanux.M α → m α) (handler : m Int) : m Int := do
  let ret ← socketCallOnWith lift NETLINK_FD do
    lift (skipCut allocCuts)
    let ret ← handler
    lift (skipCut allocCuts)
    pure ret
  _ ← socketCallOnWith lift NETLINK_FD (pure 0)
  return ret

theorem socketCallOn_factor (fd : Nat) (body : Leanux.M Int) :
    Leanux.socketCallOn fd body = socketCallOnWith (fun {_} a => a) fd body := rfl

theorem socketCallOnObserved_factor (fd : Nat) (body : PrefixM AllowedIps.RoutingCompletion Int) :
    socketCallOnObserved fd body = socketCallOnWith (fun {_} a => liftPrefix a) fd body := rfl

theorem socketCallOnAudit_factor (fd : Nat) (body : AuditM Int) :
    socketCallOnAudit fd body = socketCallOnWith (fun {_} a => liftPrefix a) fd body := rfl

theorem rxSocketCallOn_factor (fd : Nat) (body : Queues.RxHistory.Obs Int) :
    Queues.RxHistory.socketCallOn fd body = socketCallOnWith (fun {_} a => liftPrefix a) fd body := rfl

theorem netlinkRequest_factor (body : Leanux.M Int) :
    Leanux.netlinkRequest body = netlinkRequestWith (fun {_} a => a) body := rfl

theorem netlinkRequestObserved_factor (body : PrefixM AllowedIps.RoutingCompletion Int) :
    netlinkRequestObserved body = netlinkRequestWith (fun {_} a => liftPrefix a) body := rfl

theorem netlinkRequestAudit_factor (body : AuditM Int) :
    netlinkRequestAudit body = netlinkRequestWith (fun {_} a => liftPrefix a) body := rfl

theorem socketCallOnWith_projects {E F : Type} (ρ : E → Option F) (fd : Nat)
    {body : PrefixM E Int} {lower : PrefixM F Int} (hb : ProjectsPrefix ρ id body lower) :
    ProjectsPrefix ρ id (socketCallOnWith (fun {_} a => liftPrefix a) fd body)
      (socketCallOnWith (fun {_} a => liftPrefix a) fd lower) := by
  unfold socketCallOnWith
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro f
  dsimp only [id]
  apply projectsPrefix_ite ρ _ id
  · intro _; exact projectsPrefix_pure ρ id _
  · intro _
    apply projectsPrefix_bind ρ id id hb
    intro ret
    apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
    intro _
    exact projectsPrefix_pure ρ id ret

theorem netlinkRequestWith_projects {E F : Type} (ρ : E → Option F)
    {body : PrefixM E Int} {lower : PrefixM F Int} (hb : ProjectsPrefix ρ id body lower) :
    ProjectsPrefix ρ id (netlinkRequestWith (fun {_} a => liftPrefix a) body)
      (netlinkRequestWith (fun {_} a => liftPrefix a) lower) := by
  unfold netlinkRequestWith
  apply projectsPrefix_bind ρ id id
  · apply socketCallOnWith_projects ρ
    apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
    intro _
    apply projectsPrefix_bind ρ id id hb
    intro ret
    apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
    intro _
    exact projectsPrefix_pure ρ id ret
  · intro ret
    apply projectsPrefix_bind ρ id id (socketCallOnWith_projects ρ _ (projectsPrefix_pure ρ id 0))
    intro _
    exact projectsPrefix_pure ρ id ret

theorem socketCallOnWith_appends {E : Type} (fd : Nat) {body : PrefixM E Int}
    (hb : Appends body) : Appends (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply Appends.bind (Appends.lift _)
  intro f
  split
  · exact Appends.pure _
  · exact Appends.bind hb (fun ret => Appends.bind (Appends.lift _) (fun _ => Appends.pure ret))

theorem netlinkRequestWith_appends {E : Type} {body : PrefixM E Int}
    (hb : Appends body) : Appends (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply Appends.bind
    (socketCallOnWith_appends _ (Appends.bind (Appends.lift _) (fun _ =>
      Appends.bind hb (fun ret => Appends.bind (Appends.lift _) (fun _ => Appends.pure ret)))))
  intro ret
  exact Appends.bind (socketCallOnWith_appends _ (Appends.pure 0)) (fun _ => Appends.pure ret)

private theorem true_preserves {E α : Type} {a : PrefixM E α} (ha : Appends a) :
    PrefixPreserves (fun _ _ => True) (fun _ => True) a := by
  intro w h _
  obtain ⟨s,hs⟩ := ha w h
  refine ⟨s,hs,True.intro,?_⟩
  cases (runPrefix a w h).1 <;> trivial

theorem socketCallOnWith_focuses {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e) (fd : Nat)
    {body : PrefixM F Int} {lower : PrefixM E Int}
    (hb : FocusesUnder (fun _ _ => True) encode decode body lower) (hl : Appends lower) :
    FocusesUnder (fun _ _ => True) encode decode
      (socketCallOnWith (fun {_} a => liftPrefix a) fd body)
      (socketCallOnWith (fun {_} a => liftPrefix a) fd lower) := by
  unfold socketCallOnWith
  apply FocusesUnder.bind hd (FocusesUnder.lift _) (true_preserves (Appends.lift _))
  · intro f
    split
    · exact FocusesUnder.pure _
    · apply FocusesUnder.bind hd hb (true_preserves hl)
      · intro ret
        exact FocusesUnder.bind hd (FocusesUnder.lift _) (true_preserves (Appends.lift _))
          (fun _ => FocusesUnder.pure ret) (fun _ => true_preserves (Appends.pure ret))
      · intro ret
        exact true_preserves (Appends.bind (Appends.lift _) (fun _ => Appends.pure ret))
  · intro f
    split
    · exact true_preserves (Appends.pure _)
    · exact true_preserves (Appends.bind hl (fun ret => Appends.bind (Appends.lift _) (fun _ => Appends.pure ret)))

theorem netlinkRequestWith_focuses {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e)
    {body : PrefixM F Int} {lower : PrefixM E Int}
    (hb : FocusesUnder (fun _ _ => True) encode decode body lower) (hl : Appends lower) :
    FocusesUnder (fun _ _ => True) encode decode
      (netlinkRequestWith (fun {_} a => liftPrefix a) body)
      (netlinkRequestWith (fun {_} a => liftPrefix a) lower) := by
  have inner := Appends.bind (Appends.lift (skipCut allocCuts)) (fun _ =>
    Appends.bind hl (fun ret => Appends.bind (Appends.lift (skipCut allocCuts)) (fun _ => Appends.pure ret)))
  unfold netlinkRequestWith
  apply FocusesUnder.bind hd
  · apply socketCallOnWith_focuses encode decode hd
    · apply FocusesUnder.bind hd (FocusesUnder.lift _) (true_preserves (Appends.lift _))
      · intro _
        apply FocusesUnder.bind hd hb (true_preserves hl)
        · intro ret
          exact FocusesUnder.bind hd (FocusesUnder.lift _) (true_preserves (Appends.lift _))
            (fun _ => FocusesUnder.pure ret) (fun _ => true_preserves (Appends.pure ret))
        · intro ret
          exact true_preserves (Appends.bind (Appends.lift _) (fun _ => Appends.pure ret))
      · intro _
        exact true_preserves (Appends.bind hl (fun ret => Appends.bind (Appends.lift _) (fun _ => Appends.pure ret)))
    · exact inner
  · exact true_preserves (socketCallOnWith_appends _ inner)
  · intro ret
    exact FocusesUnder.bind hd
      (socketCallOnWith_focuses encode decode hd _ (FocusesUnder.pure 0) (Appends.pure 0))
      (true_preserves (socketCallOnWith_appends _ (Appends.pure 0)))
      (fun _ => FocusesUnder.pure ret) (fun _ => true_preserves (Appends.pure ret))
  · intro ret
    exact true_preserves (Appends.bind (socketCallOnWith_appends _ (Appends.pure 0)) (fun _ => Appends.pure ret))

theorem netlinkRequestWith_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e) (body : PrefixM E Int) (hb : Appends body) :
    netlinkRequestWith (fun {_} a => liftPrefix a) (focusPrefix encode decode body) =
      focusPrefix encode decode (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  funext w h
  exact netlinkRequestWith_focuses encode decode hd (FocusesUnder.focus body) hb w h True.intro

theorem socketCallOnWith_erases {E : Type} (fd : Nat)
    {body : PrefixM E Int} {original : Leanux.M Int} (hb : ErasesPrefix body original) :
    ErasesPrefix (socketCallOnWith (fun {_} a => liftPrefix a) fd body)
      (Leanux.socketCallOn fd original) := by
  rw [socketCallOn_factor]
  unfold socketCallOnWith
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro f
  apply erasesPrefix_ite
  · intro _; exact erasesPrefix_pure _
  · intro _
    apply erasesPrefix_bind hb
    intro ret
    exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure ret)

theorem netlinkRequestWith_erases {E : Type}
    {body : PrefixM E Int} {original : Leanux.M Int} (hb : ErasesPrefix body original) :
    ErasesPrefix (netlinkRequestWith (fun {_} a => liftPrefix a) body)
      (Leanux.netlinkRequest original) := by
  unfold netlinkRequestWith Leanux.netlinkRequest Leanux.socketCall
  apply erasesPrefix_bind
  · apply socketCallOnWith_erases
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    apply erasesPrefix_bind hb
    intro ret
    exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure ret)
  · intro ret
    exact erasesPrefix_bind (socketCallOnWith_erases _ (erasesPrefix_pure 0))
      (fun _ => erasesPrefix_pure ret)

end Leanux.Proofs.WG.Configuration

namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Configuration

/-- The actual wgSet dispatch arm; syscall entry and post-call waits are
separate source stages. The handler is executed once inside the real socket. -/
def dispatchSet (attrs : DeviceAttrs) : PrefixM Event Int :=
  netlinkRequestWith (fun {_} a => liftPrefix a) (liftWGObserver (setDevice attrs))

theorem dispatchSet_routing (attrs : DeviceAttrs) :
    ProjectsPrefix routingEvent id (dispatchSet attrs) (dispatchObserved (.wgSet attrs)) := by
  change ProjectsPrefix routingEvent id (dispatchSet attrs)
    (netlinkRequestObserved (liftWGObserver (wgSetDeviceObserved attrs)))
  rw [netlinkRequestObserved_factor]
  exact netlinkRequestWith_projects routingEvent ((setDevice_routing attrs).liftWGObserver _ _)

theorem dispatchSet_rx (attrs : DeviceAttrs) :
    ProjectsPrefix rxEvent id (dispatchSet attrs) (RxHistory.syscallDispatch (.wgSet attrs)) := by
  change ProjectsPrefix rxEvent id (dispatchSet attrs)
    (RxHistory.audit (netlinkRequestAudit (auditFocus (liftWGObserver (wgSetDevicePrefix attrs)))))
  rw [netlinkRequestAudit_factor]
  unfold RxHistory.audit
  rw [← netlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (auditFocus (liftWGObserver (wgSetDevicePrefix attrs))) (Appends.focus _ _ _)]
  exact netlinkRequestWith_projects rxEvent (setDevice_rx_product attrs)

theorem dispatchSet_erases (attrs : DeviceAttrs) :
    ErasesPrefix (dispatchSet attrs) (Leanux.dispatch (.wgSet attrs)) :=
  netlinkRequestWith_erases (liftWGObserver_erases (setDevice_erases attrs))

end Leanux.Proofs.WG.Queues.RoutingJoint
