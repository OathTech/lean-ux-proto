import Leanux.Proofs.WG.Roaming.RemoteConfigurationCaptureSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.EndpointAttempt
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {E F α : Type}
def beforeCall (event : WGWorld → Ambient → E) (action : WGPrefix E α) : WGPrefix E α :=
  fun g ambient => ExceptT.mk fun history =>
    runWGPrefix action g ambient (history ++ [event g ambient])
theorem run_beforeCall (event : WGWorld → Ambient → E) (action : WGPrefix E α)
    (g : WGWorld) (ambient : Ambient) (history : List E) :
    runWGPrefix (beforeCall event action) g ambient history =
      runWGPrefix action g ambient (history ++ [event g ambient]) := rfl
theorem beforeCall_projects (decode : E → Option F)
    (event : WGWorld → Ambient → E) (ignored : ∀ g ambient, decode (event g ambient) = none)
    (action : WGPrefix E α) (old : WGPrefix F α)
    (same : StateProjectsPrefix decode id action old) :
    StateProjectsPrefix decode id (beforeCall event action) old := by
  intro g ambient history
  have exactRun := same g ambient (history ++ [event g ambient])
  change runWGPrefix old g ambient (history.filterMap decode) =
    ((runWGPrefix action g ambient (history ++ [event g ambient])).1.map
      (fun (out,a) => (Prod.map id id out,a)),
      (runWGPrefix action g ambient (history ++ [event g ambient])).2.filterMap decode)
  simpa only [runWGPrefix, runStatePrefix, List.filterMap_append, List.filterMap_cons, ignored,
    List.filterMap_nil, List.append_nil] using exactRun
theorem beforeCall_erases (event : WGWorld → Ambient → E) (action : WGPrefix E α)
    (original : WG.M α) (same : ErasesStatePrefix action original) :
    ErasesStatePrefix (beforeCall event action) original := by
  intro g ambient history
  exact same g ambient (history ++ [event g ambient])
theorem beforeCall_complete (event : WGWorld → Ambient → E) (action : WGPrefix E α)
    (appends : StateAppends action) (g : WGWorld) (ambient : Ambient) (history : List E) :
    ∃ suffix, (runWGPrefix (beforeCall event action) g ambient history).2 =
      history ++ [event g ambient] ++ suffix :=
  appends g ambient (history ++ [event g ambient])
theorem beforeCall_retains (event : WGWorld → Ambient → E) (action : WGPrefix E α)
    (appends : StateAppends action) (g : WGWorld) (ambient : Ambient) (history : List E) :
    event g ambient ∈ (runWGPrefix (beforeCall event action) g ambient history).2 := by
  obtain ⟨suffix, same⟩ := beforeCall_complete event action appends g ambient history
  rw [same]
  exact List.mem_append_left _ (List.mem_append_right _ (by simp))

theorem beforeCall_appends (event : WGWorld → Ambient → E) (action : WGPrefix E α)
    (appends : StateAppends action) : StateAppends (beforeCall event action) := by
  intro g ambient history
  obtain ⟨suffix,same⟩ := beforeCall_complete event action appends g ambient history
  exact ⟨[event g ambient] ++ suffix, by simpa only [runWGPrefix, runStatePrefix, List.append_assoc] using same⟩

def fromSkbWith {m : Type → Type} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (setter : PeerId → Endpoint → m Unit)
    (pid : PeerId) (src : SkbSource) : m Unit := do
  let endpoint ← lift (endpointFromSkb src)
  if ← lift (branch .epFromSkbOk endpoint.isSome) then
    let some e := endpoint | lift (invariant "unreachable")
    setter pid e

theorem fromSkb_original (pid : PeerId) (src : SkbSource) :
    fromSkbWith (fun a => a) setPeerEndpoint pid src = setPeerEndpointFromSkb pid src := rfl
theorem fromSkb_prefix (pid : PeerId) (src : SkbSource) :
    fromSkbWith (fun a => liftWGPrefix a) Lifetimes.setPeerEndpointPrefix pid src =
      Lifetimes.setPeerEndpointFromSkbPrefix pid src := rfl

theorem fromSkb_projects (decode : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α)
    (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (setter : PeerId → Endpoint → WGPrefix E Unit)
    (setter' : PeerId → Endpoint → WGPrefix F Unit)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix decode id (lift a) (lift' a))
    (hs : ∀ pid endpoint, StateProjectsPrefix decode id (setter pid endpoint) (setter' pid endpoint))
    (pid : PeerId) (src : SkbSource) :
    StateProjectsPrefix decode id (fromSkbWith lift setter pid src)
      (fromSkbWith lift' setter' pid src) := by
  unfold fromSkbWith
  apply StateProjectsPrefix.bind decode id id (hl _)
  intro endpoint
  dsimp only [id]
  apply StateProjectsPrefix.bind decode id id (hl _)
  intro success
  dsimp only [id]
  cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact fun g => projectsPrefix_pure decode (Prod.map id id) ((),g)
  · cases endpoint with
    | none => exact hl _
    | some e => exact hs pid e

end Leanux.Proofs.WG.Roaming.EndpointAttempt
