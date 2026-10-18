import Leanux.Proofs.WG.Noise.PendingTicketRetentionFrames
import Leanux.Proofs.WG.Index.StagedSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing

theorem keys_of_ordinary (w v : WGWorld)
    (ordinary : Keypairs.Ordinary (Keypairs.snapshot w) (Keypairs.snapshot v))
    (counter : v.keypairCounter = w.keypairCounter) :
    ResidentsRetained (keypairResidents w) (keypairResidents v) := by
  have retained := ordinary_same_frontier ordinary counter
  have projected (q : WGWorld) (i : KeypairId) : keypairResidents q i =
      ((Keypairs.snapshot q).slots i).map (·.stamp) := by
    simp [keypairResidents,Keypairs.snapshot,Keypairs.cell,Option.map_map,Function.comp_def]
  intro i stamp hi
  rw [projected] at hi ⊢
  cases hc : (Keypairs.snapshot v).slots i with
  | none => simp [hc] at hi
  | some c =>
    rw [retained i c hc]
    simpa [hc] using hi

theorem next_stagingMap (w : WGWorld) (pid : PeerId) :
    nextSlots w pid = (Index.stagingPeerMap w.dev pid).bind Prod.snd := by
  cases device : w.dev with
  | none => simp [nextSlots,Index.stagingPeerMap,device]
  | some d =>
    cases peer : d.peers[pid]? <;> simp [nextSlots,Index.stagingPeerMap,device,peer]

theorem retained_of_staging_ordinary {α : Type} (action : WG.M α)
    (staging : ∀ entry, Ensures action (Index.StagingFrame entry) (fun _ => Index.StagingFrame entry))
    (ordinary : Keypairs.OrdinaryAction action) : RetainsCall action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  have effect := staging w w ambient x v after (Index.stagingFrame_refl w) run
  have keys := (ProjectedAction.iff_run_ambient _ _ _).mp ordinary w ambient x v after run
  apply view_retained w v effect.2.2 ?_ (keys_of_ordinary w v keys effect.2.2)
  intro pid kid has
  rw [next_stagingMap] at has ⊢
  cases cell : Index.stagingPeerMap v.dev pid with
  | none => simp [cell] at has
  | some pair =>
    rw [effect.2.1 pid pair cell]
    simpa [cell] using has

theorem sendStagedPackets_retained (pid : PeerId) : RetainsCall (sendStagedPackets pid) :=
  retained_of_staging_ordinary _ (Index.sendStagedPackets_staging pid)
    (Keypairs.WGTransitions.sendStagedPackets_ordinary pid)

theorem sendKeepalive_retained (pid : PeerId) : RetainsCall (sendKeepalive pid) :=
  retained_of_staging_ordinary _ (Index.sendKeepalive_staging pid)
    (Keypairs.WGTransitions.sendKeepalive_ordinary pid)

theorem sendQueuedHandshakeInitiation_retained (pid : PeerId) (retry : Bool) :
    RetainsCall (sendQueuedHandshakeInitiation pid retry) :=
  retained_of_staging_ordinary _
    (fun entry => (ensures_iff _ _ _).mpr (Index.sendQueuedHandshakeInitiation_staging pid retry entry))
    (Keypairs.SameView.ordinary (Keypairs.WGTransitions.sendQueuedHandshakeInitiation_sameSnapshot pid retry))

end Leanux.Proofs.WG.Noise.PendingTickets
