import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalSource
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims
import Leanux.Proofs.WG.Roaming.InitiationCallClaims
import Leanux.Proofs.WG.Roaming.ResponseCallClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

theorem observedReceiveTraversalCommon_facts (msg : List UInt8) (pid : PeerId) :
    Noise.Ensures (observedReceiveTraversalCommon msg pid) (fun _ => True)
      (fun hook _ => DataDoneTraversalFacts pid hook) := by
  have trivial_call {α : Type} (a : M α) :
      ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry ret final pre run
    trivial
  have hp := trivial_call (receiveTraversalPrelude msg pid)
  have ht := (ensures_iff _ _ _).mp (dataDoneTraversal_facts pid)
  have hr := trivial_call (peerPut (some pid))
  rw [ensures_iff]
  mvcgen [observedReceiveTraversalCommon, hp, ht, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem observedInitiationReceiveTraversal_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (observedInitiationReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → InitiationReceiveTraversalFacts msg cut) := by
  have trivial_call {α : Type} (a : M α) :
      ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry ret final pre run
    trivial
  have hp := (ensures_iff _ _ _).mp (initiationCallPrefix_facts msg src)
  have he := fun pid => trivial_call (setPeerEndpointFromSkb pid src)
  have hs := fun pid => trivial_call (sendHandshakeResponse pid)
  have ht := fun pid => (ensures_iff _ _ _).mp (observedReceiveTraversalCommon_facts msg pid)
  change Noise.Ensures _ _ _
  rw [ensures_iff]
  mvcgen [observedInitiationReceiveTraversal, hp, he, hs, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [InitiationReceiveTraversalFacts]

theorem observedResponseReceiveTraversal_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (observedResponseReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → ResponseReceiveTraversalFacts msg cut) := by
  have trivial_call {α : Type} (a : M α) :
      ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry ret final pre run
    trivial
  have hp := (ensures_iff _ _ _).mp (responseCallPrefix_facts msg src)
  have he := fun pid => trivial_call (setPeerEndpointFromSkb pid src)
  have hs := fun pid => trivial_call (responseBeforeCommon pid)
  have ht := fun pid => (ensures_iff _ _ _).mp (observedReceiveTraversalCommon_facts msg pid)
  change Noise.Ensures _ _ _
  rw [ensures_iff]
  mvcgen [observedResponseReceiveTraversal, hp, he, hs, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ResponseReceiveTraversalFacts]

end Leanux.Proofs.WG.TimerDiscipline
