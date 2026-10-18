import Leanux.Proofs.WG.Roaming.RemoteDriverSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def endpointObserved (pid : PeerId) (endpoint : Endpoint) : WGPrefix Event Unit :=
  RemoteConfiguration.endpointObserved Event.rx rxEvent Event.endpoint pid endpoint

def birthObserved (key : Key) (psk : Option Key) : WGPrefix Event (Except Int PeerId) :=
  RemoteConfiguration.birthObserved Event.rx rxEvent Event.birth key psk

theorem endpoint_covered (entry : RemoteMap) (pid : PeerId) (endpoint : Endpoint) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) Safe (endpointObserved pid endpoint) := by
  apply RemoteOrigin.native_focused_receipt entry Cause EventValid Event.rx rxEvent
    (fun _ => True.intro) destinationAt
    (RoutingJoint.nativeRx (setPeerEndpointPrefix pid endpoint)) (setPeerEndpoint pid endpoint)
    (StateAppends.focus _ _ _)
    (focusStatePrefix_erases _ _ (focusStatePrefix_erases _ _ (setPeerEndpointPrefix_erases pid endpoint)))
    (fun r => Event.endpoint ⟨pid,endpoint,r⟩) (fun _ run => run)
  intro r valid other remote present
  have effect := RemoteControl.setPeerEndpoint_all_remotes pid endpoint (destinationAt r.before)
    r.before r.ambientBefore r.value r.after r.ambientAfter rfl valid
  rw [effect] at present
  by_cases family : endpoint.family = AF_INET ∨ endpoint.family = AF_INET6
  · rw [RemoteControl.setterRemotes,ite_eq_left family] at present
    by_cases selected : other = pid
    · subst other
      exact Or.inr ⟨rfl,by simpa only [updateRemote,ite_true,Option.some.injEq] using present,family⟩
    · exact Or.inl (by simpa only [updateRemote,selected,ite_false] using present)
  · exact Or.inl (by simpa only [RemoteControl.setterRemotes,ite_eq_right family] using present)

theorem birth_covered (entry : RemoteMap) (key : Key) (psk : Option Key) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) Safe (birthObserved key psk) := by
  apply RemoteOrigin.native_focused_receipt entry Cause EventValid Event.rx rxEvent
    (fun _ => True.intro) destinationAt
    (RoutingJoint.nativeRx (peerCreateMixed key psk)) (peerCreate key psk)
    (StateAppends.focus _ _ _)
    (focusStatePrefix_erases _ _ (focusStatePrefix_erases _ _ (peerCreateMixed_erases key psk)))
    (fun r => Event.birth (RemoteConfiguration.birthReceipt key psk r))
    (fun r run => RemoteConfiguration.birthReceipt_valid key psk r run)
  intro r valid pid remote present
  have effect := RemoteBirth.peerCreate_remotes key psk (destinationAt r.before)
    r.before r.ambientBefore r.value r.after r.ambientAfter rfl valid
  rw [effect] at present
  left
  cases result : r.value with
  | error code => simpa only [result,RemoteBirth.birthRemotes] using present
  | ok born =>
    simp only [result,RemoteBirth.birthRemotes] at present
    split at present
    · cases present
    · exact present

def receiveStepObserved : PrefixM Event Bool :=
  receiptObserved (focus Origins.HistoryAdapters.receiveStep) Event.receive

theorem receiveStep_covered (entry : RemoteMap) :
    PrefixPreserves (Inv entry) Safe receiveStepObserved := by
  apply RemoteOrigin.focused_receipt entry Cause EventValid Event.rx rxEvent
    (fun _ => True.intro) (fun w : World => destinationAt w.wg)
    (fun (_ : Bool) w => destinationAt w.wg)
    Origins.HistoryAdapters.receiveStep (liftWG receiveStep) (Appends.focus _ _ _)
    Origins.HistoryAdapters.receiveStep_erases Event.receive (fun _ run => run)
  exact fun r run pid remote present => ReceiveStepRemote.run_origin r run pid remote present

theorem receiveStep_projects :
    ProjectsPrefix rxEvent id receiveStepObserved Origins.HistoryAdapters.receiveStep :=
  receiptObserved_projects (fun _ => rfl)
    ((Appends.focus _ _ _).project_focus Event.rx rxEvent (fun _ => rfl))

theorem receiveStep_appends : Appends receiveStepObserved :=
  (Appends.focus _ _ _).receiptObserved

def receiveIterationObserved : PrefixM Event IterResult :=
  workerIterPrefix .receiveWorker none receiveStepObserved
    (liftPrefix (Env.condResched .receiveWorker))

theorem receiveIteration_covered (entry : RemoteMap) :
    PrefixPreserves (Inv entry) Safe receiveIterationObserved := by
  apply workerIterPrefix_preserves _ _ (safe entry) (receiveStep_covered entry)
  apply PrefixEnsures.lift
  · exact safe entry
  · intro h w value final pre run
    exact ⟨pre.1.retained ((hoare_iff_run _ _ _).mp
      (RemoteWorkers.product_store (destinationAt w.wg) _ (condResched_sameKernel _))
      w value final (RemoteRetained.refl _) run),pre.2⟩

theorem receiveIteration_projects :
    ProjectsPrefix rxEvent id receiveIterationObserved Origins.HistoryAdapters.receiveIteration := by
  unfold receiveIterationObserved Origins.HistoryAdapters.receiveIteration workerIterPrefix
  apply projectsPrefix_bind rxEvent id id receiveStep_projects
  intro more
  dsimp only [id]
  split
  · exact projectsPrefix_pure _ _ _
  · apply projectsPrefix_bind rxEvent id id (projectsPrefix_lift _ _)
    intro yes
    exact projectsPrefix_pure _ _ _

theorem receiveIteration_appends : Appends receiveIterationObserved := by
  unfold receiveIterationObserved workerIterPrefix
  apply receiveStep_appends.bind
  intro more
  split
  · exact Appends.pure _
  · exact (Appends.lift _).bind (fun _ => Appends.pure _)

end Leanux.Proofs.WG.Roaming.RemoteDriver
