import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffectsMatching
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsEmbedding

/-! Natural matching between two embeddings of the actual HC observer. The
larger journal retains the old combined history, not just its HC filter. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources

private theorem native_projects (ρ : E → Option F) (action : WG.M α) :
    StateProjectsPrefix ρ id (liftWGPrefix action) (liftWGPrefix action) := by
  intro w a h
  change ((action.run w).run a,h.filterMap ρ) =
    (((action.run w).run a).map (fun ((x,v),b) => ((x,v),b)),h.filterMap ρ)
  cases (action.run w).run a <;> rfl

theorem observedOps_natural (ρ : E → Option F)
    (eg : HandshakeCausal.Event → E) (dg : E → Option HandshakeCausal.Event)
    (et : HandshakeCausal.Event → F) (dt : F → Option HandshakeCausal.Event)
    (enc : ∀ e, ρ (eg e) = some (et e)) (dec : ∀ e, dg e = (ρ e).bind dt)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) (mac : HandshakeMac) :
    HandshakeWorker.OpsProjects ρ (HandshakeWorker.observedOps eg dg sg kg mac)
      (HandshakeWorker.observedOps et dt st kt mac) where
  step := native_projects ρ
  session := fun pid => callback_projects ρ eg et enc _ _ _ _ (hs pid)
  modifyPeer := fun _ _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  create := fun _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  mac := fun _ _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  send := fun _ _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  derived := fun _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  traversal := fun _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  sent := fun _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  cookie := fun _ _ => native_projects ρ _
  initiation := fun _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  response := fun _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  endpoint := fun _ _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  complete := fun _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  keepalive := fun pid => callback_projects ρ eg et enc _ _ _ _ (hk pid)
  received := fun _ => CompletionEffects.state_focus_matching ρ eg dg et dt enc dec _
  put := fun _ => native_projects ρ _
  cookieConsume := fun _ => native_projects ρ _

theorem effects_natural (ρ : E → Option F)
    (eg : HandshakeCausal.Event → E) (dg : E → Option HandshakeCausal.Event)
    (et : HandshakeCausal.Event → F) (dt : F → Option HandshakeCausal.Event)
    (enc : ∀ e, ρ (eg e) = some (et e)) (dec : ∀ e, dg e = (ρ e).bind dt)
    (effects : TimerEffects.Ops (WGPrefix E))
    (he : TimerEffects.Ops.Projects ρ effects TimerEffects.lifted)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) (mac : HandshakeMac) :
    HandshakeWorker.OpsProjects ρ
      (withEffects (HandshakeWorker.observedOps eg dg sg kg mac) eg effects)
      (HandshakeWorker.observedOps et dt st kt mac) := by
  have h := withEffects_projects ρ eg et enc _ _ effects TimerEffects.lifted
    (observedOps_natural ρ eg dg et dt enc dec sg st kg kt hs hk mac) he
  rwa [withEffects_neutral] at h

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
