import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTerminalSource

/-! Exact projections for branch-labelled native terminal frees. The free
callback is checked at the actual loop position; all preceding observations
and the first Stop remain intact. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Terminal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues AuthenticatedEffects
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem create_projects (ρ : E → Option F)
    {g : StagedDisposal.TxSource.Ops E} {t : StagedDisposal.TxSource.Ops F}
    (h : StagedDisposal.TxSource.Ops.Projects ρ g t)
    (free : Reason → SkbId → PrefixM E Unit)
    (hf : ∀ reason skb, ProjectsPrefix ρ id (free reason skb) (t.access (freeTxSkbPrefix skb)))
    (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix ρ id (createWith g free pid item) (StagedDisposal.TxSource.create t pid item) := by
  rw [← create_factor]
  unfold createWith
  repeat' first
    | exact hf _ _
    | with_reducible exact StagedDisposal.TxSource.publish_projects ρ h _ _
    | disposal_tx_project h ρ

theorem dispose_projects (ρ : E → Option F)
    {g : StagedDisposal.TxSource.Ops E} {t : StagedDisposal.TxSource.Ops F}
    (h : StagedDisposal.TxSource.Ops.Projects ρ g t)
    (free : SkbId → PrefixM E Unit)
    (hf : ∀ skb, ProjectsPrefix ρ id (free skb) (t.access (freeTxSkbPrefix skb)))
    (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ProjectsPrefix ρ id (disposeWith g free pid item key) (StagedDisposal.TxSource.dispose t pid item key) := by
  rw [← dispose_factor]
  unfold disposeWith
  repeat' first
    | exact hf _
    | disposal_tx_project h ρ

theorem body_projects (ρ : E → Option F) {g : CompletionEffects.Ops E} {t : CompletionEffects.Ops F}
    (h : CompletionEffects.Ops.Projects ρ g t)
    (cg : PeerId → List SkbId → PrefixM E Unit) (ct : PeerId → List SkbId → PrefixM F Unit)
    (hc : ∀ pid item, ProjectsPrefix ρ id (cg pid item) (ct pid item))
    (dead : PeerId → List SkbId → DataPacket → PrefixM E Bool)
    (hd : ∀ pid item packet, ProjectsPrefix ρ id (dead pid item packet) (t.dispose pid item packet.keypair))
    (pid : PeerId) (first : Option (List SkbId)) :
    ProjectsPrefix ρ id (bodyWith g cg dead pid first) (CompletionEffects.bodySourceWith t ct pid first) := by
  rw [← body_factor]
  unfold bodyWith TxDisposition.andObs
  repeat' first
    | exact hc _ _
    | exact hd _ _ _
    | completion_effects_project h ρ

theorem step_projects (ρ : E → Option F) {g : CompletionEffects.Ops E} {t : CompletionEffects.Ops F}
    (h : CompletionEffects.Ops.Projects ρ g t)
    (cg : PeerId → List SkbId → PrefixM E Unit) (ct : PeerId → List SkbId → PrefixM F Unit)
    (hc : ∀ pid item, ProjectsPrefix ρ id (cg pid item) (ct pid item))
    (dead : PeerId → List SkbId → DataPacket → PrefixM E Bool)
    (hd : ∀ pid item packet, ProjectsPrefix ρ id (dead pid item packet) (t.dispose pid item packet.keypair))
    (pid : PeerId) :
    ProjectsPrefix ρ id (stepWith g cg dead pid) (CompletionEffects.stepSourceWith t ct pid) := by
  unfold stepWith CompletionEffects.stepSourceWith
  repeat' first
    | with_reducible exact body_projects ρ h cg ct hc dead hd _ _
    | completion_effects_project h ρ

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Terminal
