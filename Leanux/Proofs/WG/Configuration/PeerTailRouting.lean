import Leanux.Proofs.WG.Configuration.AllowedIpSource
import Leanux.Proofs.WG.AllowedIps.RoutingCompletions

/-! Source-shaped completion observation of the original allowed-IP loop.
The continuation boundary preserves early cleanup and the final iteration
record. Semantic input shape and target residency are separate from erasure. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps

def PeerAddressShape (a : PeerAttrs) : Prop :=
  ∀ ip, AllowedIpEntry.attrs ip ∈ a.allowedIps.getD [] → AddressShape ip

def peerConfigOutObserved (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    WGPrefix RoutingCompletion Int := do
  liftWGPrefix (peerPut peer)
  _ ← liftWGPrefix (branch .peerZeroPsk a.presharedKey.isSome)
  return ret

/-- One control sequence, interpreted in the actual native observer or through
the runner's adapter. The continuation remains in its caller's monad. -/
def peerAllowedIpsObservedWith {m : Type → Type} [Monad m]
    (lift : {α : Type} → WGPrefix RoutingCompletion α → m α)
    (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (next : Int → m Int) : m Int :=
  peerAllowedIpsWith (fun d b => lift (liftWGPrefix (branch d b)))
    (fun ip => lift (completedAllowedip pid ip))
    (fun ret => lift (peerConfigOutObserved a peer ret)) a next

/-- Arbitrary product continuations retain their original interface. -/
def peerAllowedIpsObserved (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → PrefixM RoutingCompletion Int) : PrefixM RoutingCompletion Int :=
  peerAllowedIpsObservedWith (fun {_} g => liftWGObserver g) a peer pid next

/-- The concrete WireGuard tail uses native WG and Ambient endpoints. -/
def peerAllowedIpsObservedWG (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → WGPrefix RoutingCompletion Int) : WGPrefix RoutingCompletion Int :=
  peerAllowedIpsObservedWith (fun {_} g => g) a peer pid next

theorem peerConfigOutObserved_erases (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    ErasesStatePrefix (peerConfigOutObserved a peer ret)
      (do peerPut peer; _ ← branch .peerZeroPsk a.presharedKey.isSome; pure ret) := by
  unfold peerConfigOutObserved
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure _))

theorem peerAllowedIpsObservedWG_erases (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → WGPrefix RoutingCompletion Int) (source : Int → WG.M Int)
    (hn : ∀ ret, ErasesStatePrefix (next ret) (source ret)) :
    ErasesStatePrefix (peerAllowedIpsObservedWG a peer pid next)
      (peerAllowedIpsSource a peer pid source) := by
  unfold peerAllowedIpsObservedWG peerAllowedIpsObservedWith peerAllowedIpsSource peerAllowedIpsWith peerConfigOutObserved
  simp only [bind_assoc, pure_bind, monadLift_self, liftWGPrefix]
  repeat' first
    | with_reducible exact hn _
    | with_reducible exact completedAllowedip_erases _ _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem peerAllowedIpsObserved_erases (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → PrefixM RoutingCompletion Int) (source : Int → Leanux.M Int)
    (hn : ∀ ret, ErasesPrefix (next ret) (source ret)) :
    ErasesPrefix (peerAllowedIpsObserved a peer pid next) (peerAllowedIpsSource a peer pid source) := by
  unfold peerAllowedIpsObserved peerAllowedIpsObservedWith peerAllowedIpsSource peerAllowedIpsWith peerConfigOutObserved
  simp only [bind_assoc, pure_bind, liftWGObserver_bind]
  repeat' first
    | exact hn _
    | exact liftWGObserver_erases (completedAllowedip_erases _ _)
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals
    intro w h
    try simp only [liftWGObserver_run, runWGPrefix_lift]
    rfl

theorem peerConfigOutObserved_preserves (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (peerConfigOutObserved a peer ret) (fun _ h w _ => CompletionState initial h w) := by
  unfold peerConfigOutObserved
  apply StatePrefixEnsures.bind (completion_lift_retains_wg initial _ (peerPut_retainsRouting peer))
  intro _
  have hb : StatePrefixPreserves (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (liftWGPrefix (branch .peerZeroPsk a.presharedKey.isSome)) := by
    apply StatePrefixEnsures.lift _ (fun _ _ _ h => h.1)
    intro h w ambient x v ambient' hi hr
    exact (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch .peerZeroPsk a.presharedKey.isSome)
        (fun w => CompletionState initial h w)) w ambient x v ambient' hi hr
  apply StatePrefixEnsures.bind hb
  intro _
  exact StatePrefixEnsures.pure _ (fun _ _ _ h => h.1) (fun _ _ _ h => h)

def AllowedIpLoopState (initial : FlatTable × FlatTable) (pid : PeerId)
    (acc : Option Int × Int) (h : List RoutingCompletion) (w : WGWorld) : Prop :=
  match acc.1 with
  | none => CompletionTarget initial pid h w
  | some _ => CompletionState initial h w

def AllowedIpStepState (initial : FlatTable × FlatTable) (pid : PeerId)
    (step : ForInStep (Option Int × Int)) (h : List RoutingCompletion) (w : WGWorld) : Prop :=
  match step with
  | .done acc => AllowedIpLoopState initial pid acc h w
  | .yield acc => acc.1 = none ∧ CompletionTarget initial pid h w

theorem allowedIpLoop_safe (h : AllowedIpLoopState initial pid acc history w) :
    CompletionSafe initial history := by
  rcases acc with ⟨early, ret⟩
  cases early
  · exact h.1.1
  · exact h.1

theorem forIn_completion_early {S : Type} (project : S → WGWorld) (xs : List α) (ret : Int)
    (g : α → (Option Int × Int) → PrefixT RoutingCompletion S (ForInStep (Option Int × Int)))
    (hg : ∀ x ∈ xs, ∀ ret, PrefixEnsures (fun h w => CompletionTarget initial pid h (project w)) (CompletionSafe initial)
      (g x (none, ret)) (fun step h w => AllowedIpStepState initial pid step h (project w))) :
    PrefixEnsures (fun h w => CompletionTarget initial pid h (project w)) (CompletionSafe initial)
      (forIn xs (none, ret) g) (fun acc h w => AllowedIpLoopState initial pid acc h (project w)) := by
  induction xs generalizing ret with
  | nil =>
    simpa only [List.forIn_nil] using
      (PrefixEnsures.pure (fun _ _ h => h.1.1) (fun _ _ h => h) :
        PrefixEnsures (fun h w => CompletionTarget initial pid h (project w)) (CompletionSafe initial)
          (pure (none, ret)) (fun acc h w => AllowedIpLoopState initial pid acc h (project w)))
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply PrefixEnsures.bind (hg x (by simp) ret)
    intro step
    cases step with
    | done acc => exact PrefixEnsures.pure (fun _ _ h => allowedIpLoop_safe h) (fun _ _ h => h)
    | yield acc =>
      rcases acc with ⟨early, ret⟩
      intro w h hi
      have he : early = none := hi.1
      subst early
      exact ih ret (fun y hy => hg y (by simp [hy])) w h hi.2

theorem forIn_completion_early_wg (xs : List α) (ret : Int)
    (g : α → (Option Int × Int) → WGPrefix RoutingCompletion (ForInStep (Option Int × Int)))
    (hg : ∀ x ∈ xs, ∀ ret, StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (g x (none, ret)) (fun step h w _ => AllowedIpStepState initial pid step h w)) :
    StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (forIn xs (none, ret) g) (fun acc h w _ => AllowedIpLoopState initial pid acc h w) := by
  induction xs generalizing ret with
  | nil =>
    simpa only [List.forIn_nil] using
      (StatePrefixEnsures.pure _ (fun _ _ _ h => h.1.1) (fun _ _ _ h => h) :
        StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
          (pure (none, ret)) (fun acc h w _ => AllowedIpLoopState initial pid acc h w))
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StatePrefixEnsures.bind (hg x (by simp) ret)
    intro step
    cases step with
    | done acc => exact StatePrefixEnsures.pure _ (fun _ _ _ h => allowedIpLoop_safe h) (fun _ _ _ h => h)
    | yield acc =>
      rcases acc with ⟨early, ret⟩
      intro w ambient h hi
      have he : early = none := hi.1
      subst early
      exact ih ret (fun y hy => hg y (by simp [hy])) w ambient h hi.2

theorem peerAllowedIpsObservedWG_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) (peer : Option PeerId) (pid : PeerId)
    (next : Int → WGPrefix RoutingCompletion Int)
    (hn : ∀ ret, StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (next ret) (fun _ h w _ => CompletionState initial h w)) :
    StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (peerAllowedIpsObservedWG a peer pid next) (fun _ h w _ => CompletionState initial h w) := by
  have out ret : StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (peerConfigOutObserved a peer ret) (fun _ h w _ => CompletionState initial h w) :=
    (peerConfigOutObserved_preserves initial a peer ret).consequence
      (fun _ _ _ h => h.1) (fun _ _ _ _ h => h)
  have branch_spec (d : Decision) (value : Bool) :
      StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
        (liftWGPrefix (branch d value)) (fun _ h w _ => CompletionTarget initial pid h w) := by
    apply StatePrefixEnsures.lift _ (fun _ _ _ h => h.1.1)
    intro h w ambient x v ambient' hi hr
    exact (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch d value) (fun w => CompletionTarget initial pid h w))
      w ambient x v ambient' hi hr
  unfold peerAllowedIpsObservedWG peerAllowedIpsObservedWith peerAllowedIpsWith
  apply StatePrefixEnsures.bind (branch_spec _ _)
  intro has
  split
  · dsimp only
    change StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial) (_ >>= _) _
    refine StatePrefixEnsures.bind (forIn_completion_early_wg _ _ _ ?_) ?_
    · intro entry he ret
      dsimp only
      apply StatePrefixEnsures.bind (branch_spec _ _)
      intro _
      cases entry with
      | malformed =>
        apply StatePrefixEnsures.bind (branch_spec _ _)
        intro _
        apply StatePrefixEnsures.bind (out (-EINVAL))
        intro result
        exact StatePrefixEnsures.pure _ (fun _ _ _ h => h.1) (fun _ _ _ h => h)
      | attrs ip =>
        apply StatePrefixEnsures.bind (branch_spec _ _)
        intro _
        apply StatePrefixEnsures.bind (completedAllowedip_preserves initial pid ip (shape ip he))
        intro result
        apply StatePrefixEnsures.bind (branch_spec _ _)
        intro bad
        split
        · apply StatePrefixEnsures.bind (out result)
          intro result'
          exact StatePrefixEnsures.pure _ (fun _ _ _ h => h.1) (fun _ _ _ h => h)
        · exact StatePrefixEnsures.pure _ (fun _ _ _ h => h.1.1) (fun _ _ _ h => ⟨rfl, h⟩)
    · intro acc
      rcases acc with ⟨early, ret⟩
      cases early with
      | some result => exact StatePrefixEnsures.pure _ (fun _ _ _ h => h.1) (fun _ _ _ h => h)
      | none =>
        apply StatePrefixEnsures.bind (branch_spec _ _)
        intro _
        exact hn ret
  · exact hn 0

theorem peerAllowedIpsObserved_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) (peer : Option PeerId) (pid : PeerId)
    (next : Int → PrefixM RoutingCompletion Int)
    (hn : ∀ ret, PrefixEnsures (fun h (w : World) => CompletionTarget initial pid h w.wg) (CompletionSafe initial)
      (next ret) (fun _ h (w : World) => CompletionState initial h w.wg)) :
    PrefixEnsures (fun h (w : World) => CompletionTarget initial pid h w.wg) (CompletionSafe initial)
      (peerAllowedIpsObserved a peer pid next) (fun _ h (w : World) => CompletionState initial h w.wg) := by
  have out ret : PrefixEnsures (fun h (w : World) => CompletionTarget initial pid h w.wg) (CompletionSafe initial)
      (liftWGObserver (peerConfigOutObserved a peer ret)) (fun _ h (w : World) => CompletionState initial h w.wg) :=
    ((peerConfigOutObserved_preserves initial a peer ret).liftWGObserver).consequence
      (fun _ _ h => h.1) (fun _ _ _ h => h)
  have branch_spec (d : Decision) (value : Bool) :
      PrefixEnsures (fun h (w : World) => CompletionTarget initial pid h w.wg) (CompletionSafe initial)
        (liftWGObserver (liftWGPrefix (branch d value))) (fun _ h (w : World) => CompletionTarget initial pid h w.wg) := by
    have hn : StatePrefixPreserves (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
        (liftWGPrefix (branch d value)) := by
      apply StatePrefixEnsures.lift _ (fun _ _ _ h => h.1.1)
      intro h w ambient x v ambient' hi hr
      exact (hoare_iff_run_ambient _ _ _).mp
        (hoare_liftAmbient (AmbientM.branch d value) (fun w => CompletionTarget initial pid h w))
        w ambient x v ambient' hi hr
    exact hn.liftWGObserver
  unfold peerAllowedIpsObserved peerAllowedIpsObservedWith peerAllowedIpsWith
  apply PrefixEnsures.bind (branch_spec _ _)
  intro has
  split
  · dsimp only
    change PrefixEnsures (fun h (w : World) => CompletionTarget initial pid h w.wg) (CompletionSafe initial) (_ >>= _) _
    refine PrefixEnsures.bind (forIn_completion_early World.wg _ _ _ ?_) ?_
    · intro entry he ret
      dsimp only
      apply PrefixEnsures.bind (branch_spec _ _)
      intro _
      cases entry with
      | malformed =>
        apply PrefixEnsures.bind (branch_spec _ _)
        intro _
        apply PrefixEnsures.bind (out (-EINVAL))
        intro result
        exact PrefixEnsures.pure (fun _ _ h => h.1) (fun _ _ h => h)
      | attrs ip =>
        apply PrefixEnsures.bind (branch_spec _ _)
        intro _
        apply PrefixEnsures.bind ((completedAllowedip_preserves initial pid ip (shape ip he)).liftWGObserver)
        intro result
        apply PrefixEnsures.bind (branch_spec _ _)
        intro bad
        split
        · apply PrefixEnsures.bind (out result)
          intro result'
          exact PrefixEnsures.pure (fun _ _ h => h.1) (fun _ _ h => h)
        · exact PrefixEnsures.pure (fun _ _ h => h.1.1) (fun _ _ h => ⟨rfl, h⟩)
    · intro acc
      rcases acc with ⟨early, ret⟩
      cases early with
      | some result => exact PrefixEnsures.pure (fun _ _ h => h.1) (fun _ _ h => h)
      | none =>
        apply PrefixEnsures.bind (branch_spec _ _)
        intro _
        exact hn ret
  · exact hn 0


end Leanux.Proofs.WG.Configuration
