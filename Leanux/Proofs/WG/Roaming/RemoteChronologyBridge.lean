import Leanux.Proofs.WG.Roaming.RemoteDriverCaptureSource
import Leanux.Proofs.WG.Roaming.ReceiveStepSetterEffects
import Leanux.Proofs.WG.Roaming.RemoteChronologySource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Queues Leanux.Proofs.Logged

/-- A proof-level classification of the existing completed-call receipt.
No second observer or execution is added to the journal. -/
noncomputable def receiveSetter (r : RunWitness Bool) : Option (PeerId × Remote) := by
  classical
  exact if valid : r.Valid (liftWG receiveStep) then
    (Classical.choose (ReceiveStepRemote.complete r valid)).setter
  else none

def setterEffect (setter : Option (PeerId × Remote)) (pid : PeerId) : Option (Option Remote) :=
  match setter with
  | none => none
  | some (selected,remote) => if pid = selected then some (some remote) else none

noncomputable def effect : Effect RemoteDriver.Event
  | .rx (.consumed _ _ _ receipt), pid =>
    if receipt.endpoint.family = AF_INET ∨ receipt.endpoint.family = AF_INET6 then
      setterEffect (some (receipt.peer,destination receipt.endpoint)) pid
    else none
  | .rx _, _ => none
  | .receive run, pid => setterEffect (receiveSetter run) pid
  | .endpoint run, pid =>
    if run.endpoint.family = AF_INET ∨ run.endpoint.family = AF_INET6 then
      setterEffect (some (run.peer,destination run.endpoint)) pid
    else none
  | .birth receipt, pid =>
    match receipt.result with
    | .error _ => none
    | .ok born => if born = pid then some none else none

theorem apply_setter (setter : Option (PeerId × Remote)) (entry : RemoteMap) :
    (fun pid => match setterEffect setter pid with
      | none => entry pid
      | some remote => remote) = ReceiveStepRemote.setterMap entry setter := by
  funext pid
  cases setter with
  | none => rfl
  | some pair =>
    obtain ⟨selected,remote⟩ := pair
    by_cases same : pid = selected <;>
      simp only [setterEffect,ReceiveStepRemote.setterMap,updateRemote,same,ite_true,ite_false]

theorem endpoint_effect (r : RemoteConfiguration.EndpointRun) (valid : r.Valid) :
    RemoteRetained (applyEffect effect (.endpoint r) (destinationAt r.run.before))
      (destinationAt r.run.after) := by
  have changed := r.effect valid
  change destinationAt r.run.after =
    RemoteControl.setterRemotes (destinationAt r.run.before) r.peer r.endpoint at changed
  apply RemoteRetained.of_eq
  rw [changed]
  funext pid
  by_cases family : r.endpoint.family = AF_INET ∨ r.endpoint.family = AF_INET6 <;>
    by_cases selected : pid = r.peer <;>
    simp only [RemoteControl.setterRemotes,updateRemote,applyEffect,effect,setterEffect,
      family,selected,ite_true,ite_false]

theorem birth_effect (r : PeerCreateReceipt) (valid : DriverTags.PeerCreateValid r) :
    RemoteRetained (applyEffect effect (.birth r) (remoteMap r.before)) (remoteMap r.after) := by
  have changed := (RemoteBirth.receipt_effect r valid).2
  apply RemoteRetained.of_eq
  rw [changed]
  funext pid
  cases result : r.result with
  | error code => simp only [RemoteBirth.birthRemotes,applyEffect,effect,result]
  | ok born =>
    by_cases selected : born = pid <;>
      simp only [RemoteBirth.birthRemotes,result,applyEffect,effect,selected,ite_true,ite_false]

theorem receive_effect (r : RunWitness Bool) (valid : r.Valid (liftWG receiveStep)) :
    RemoteRetained (applyEffect effect (.receive r) (destinationAt r.before.wg))
      (destinationAt r.after.wg) := by
  have chosen := Classical.choose_spec (ReceiveStepRemote.complete r valid)
  have changed := ReceiveStepRemote.observation_setter_effect _ chosen.2
  have application : applyEffect effect (.receive r) (destinationAt r.before.wg) =
      ReceiveStepRemote.setterMap (destinationAt r.before.wg) (receiveSetter r) :=
    apply_setter _ _
  rw [application,receiveSetter,dite_eq_left valid]
  rw [chosen.1.1,chosen.1.2.1] at changed
  exact changed

theorem receive_cause (r : RunWitness Bool) (pid : PeerId) (remote : Remote)
    (selected : receiveSetter r = some (pid,remote)) :
    RemoteDriver.Cause (.receive r) pid remote := by
  unfold receiveSetter at selected
  split at selected
  next valid =>
    have chosen := Classical.choose_spec (ReceiveStepRemote.complete r valid)
    exact ⟨_,chosen.1,
      ReceiveStepRemote.observation_setter_authenticated _ chosen.2 pid remote selected⟩
  next invalid => cases selected

theorem consume_effect (occurrence id : Nat) (stamp : Lifetimes.PacketStamp)
    (r : RxDisposition.ConsumeReceipt) (valid : r.run.Valid (consumeDataDone r.peer r.packet r.endpoint)) :
    RemoteRetained (applyEffect effect (.rx (.consumed occurrence id stamp r))
      (destinationAt r.run.before)) (destinationAt r.run.after) := by
  have changed := RemoteControl.consumeDataDone_all_remotes (destinationAt r.run.before)
    r.peer r.packet r.endpoint r.run.before r.run.ambientBefore r.run.value
      r.run.after r.run.ambientAfter rfl valid
  have applied : applyEffect effect (.rx (.consumed occurrence id stamp r))
      (destinationAt r.run.before) =
      RemoteControl.setterRemotes (destinationAt r.run.before) r.peer r.endpoint := by
    funext pid
    by_cases family : r.endpoint.family = AF_INET ∨ r.endpoint.family = AF_INET6 <;>
      by_cases selected : pid = r.peer <;>
      simp only [RemoteControl.setterRemotes,updateRemote,applyEffect,effect,setterEffect,
        family,selected,ite_true,ite_false]
  rw [applied]
  exact changed

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
