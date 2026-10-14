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
    PrefixM RoutingCompletion Int := do
  liftPrefix (peerPut peer)
  _ ← liftPrefix (branch .peerZeroPsk a.presharedKey.isSome)
  return ret

def peerAllowedIpsObserved (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → PrefixM RoutingCompletion Int) : PrefixM RoutingCompletion Int := do
  let mut ret : Int := 0
  if ← liftPrefix (branch .peerHasAips a.allowedIps.isSome) then
    for entry in a.allowedIps.getD [] do
      _ ← liftPrefix (branch .peerAipsIter true)
      match entry with
      | .malformed =>
        _ ← liftPrefix (branch .peerAipParseErr true)
        return ← peerConfigOutObserved a peer (-EINVAL)
      | .attrs ip =>
        _ ← liftPrefix (branch .peerAipParseErr false)
        ret ← completedAllowedip pid ip
        if ← liftPrefix (branch .peerAipErr (ret < 0)) then
          return ← peerConfigOutObserved a peer ret
    _ ← liftPrefix (branch .peerAipsIter false)
  next ret

theorem peerConfigOutObserved_erases (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    ErasesPrefix (peerConfigOutObserved a peer ret)
      (do peerPut peer; _ ← branch .peerZeroPsk a.presharedKey.isSome; pure ret) := by
  unfold peerConfigOutObserved
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
    erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _))

theorem peerAllowedIpsObserved_erases (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → PrefixM RoutingCompletion Int) (source : Int → M Int)
    (hn : ∀ ret, ErasesPrefix (next ret) (source ret)) :
    ErasesPrefix (peerAllowedIpsObserved a peer pid next) (peerAllowedIpsSource a peer pid source) := by
  unfold peerAllowedIpsObserved peerAllowedIpsSource peerConfigOutObserved
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact hn _
    | with_reducible exact peerConfigOutObserved_erases _ _ _
    | with_reducible exact completedAllowedip_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem peerConfigOutObserved_preserves (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (peerConfigOutObserved a peer ret) (fun _ => CompletionState initial) := by
  unfold peerConfigOutObserved
  apply PrefixEnsures.bind (completion_lift_retains initial _ (peerPut_retainsRouting peer))
  intro _
  apply PrefixEnsures.bind (completion_lift_retains initial _
    (RetainsRoutingCall.of_same (routing_kernel _ (sameKernel_branch _ _))))
  intro _
  exact PrefixEnsures.pure (fun _ _ h => h.1) (fun _ _ h => h)

def AllowedIpLoopState (initial : FlatTable × FlatTable) (pid : PeerId)
    (acc : Option Int × Int) (h : List RoutingCompletion) (w : World) : Prop :=
  match acc.1 with
  | none => CompletionTarget initial pid h w
  | some _ => CompletionState initial h w

def AllowedIpStepState (initial : FlatTable × FlatTable) (pid : PeerId)
    (step : ForInStep (Option Int × Int)) (h : List RoutingCompletion) (w : World) : Prop :=
  match step with
  | .done acc => AllowedIpLoopState initial pid acc h w
  | .yield acc => acc.1 = none ∧ CompletionTarget initial pid h w

theorem allowedIpLoop_safe (h : AllowedIpLoopState initial pid acc history w) :
    CompletionSafe initial history := by
  rcases acc with ⟨early, ret⟩
  cases early
  · exact h.1.1
  · exact h.1

theorem forIn_completion_early (xs : List α) (ret : Int)
    (g : α → (Option Int × Int) → PrefixM RoutingCompletion (ForInStep (Option Int × Int)))
    (hg : ∀ x ∈ xs, ∀ ret, PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial)
      (g x (none, ret)) (AllowedIpStepState initial pid)) :
    PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial)
      (forIn xs (none, ret) g) (AllowedIpLoopState initial pid) := by
  induction xs generalizing ret with
  | nil =>
    simpa only [List.forIn_nil] using
      (PrefixEnsures.pure (fun _ _ h => h.1.1) (fun _ _ h => h) :
        PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial)
          (pure (none, ret)) (AllowedIpLoopState initial pid))
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

 theorem peerAllowedIpsObserved_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) (peer : Option PeerId) (pid : PeerId)
    (next : Int → PrefixM RoutingCompletion Int)
    (hn : ∀ ret, PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial)
      (next ret) (fun _ => CompletionState initial)) :
    PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial)
      (peerAllowedIpsObserved a peer pid next) (fun _ => CompletionState initial) := by
  have out ret : PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial)
      (peerConfigOutObserved a peer ret) (fun _ => CompletionState initial) :=
    (peerConfigOutObserved_preserves initial a peer ret).consequence
      (fun _ _ h => h.1) (fun _ _ _ h => h)
  unfold peerAllowedIpsObserved
  apply PrefixEnsures.bind (completion_lift_same initial pid _
    (routing_kernel _ (sameKernel_branch _ _)))
  intro has
  split
  · dsimp only
    change PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial) (_ >>= _) _
    refine PrefixEnsures.bind (forIn_completion_early _ _ _ ?_) ?_
    · intro entry he ret
      dsimp only
      apply PrefixEnsures.bind (completion_lift_same initial pid _
        (routing_kernel _ (sameKernel_branch _ _)))
      intro _
      cases entry with
      | malformed =>
        apply PrefixEnsures.bind (completion_lift_same initial pid _
          (routing_kernel _ (sameKernel_branch _ _)))
        intro _
        apply PrefixEnsures.bind (out (-EINVAL))
        intro result
        exact PrefixEnsures.pure (fun _ _ h => h.1) (fun _ _ h => h)
      | attrs ip =>
        apply PrefixEnsures.bind (completion_lift_same initial pid _
          (routing_kernel _ (sameKernel_branch _ _)))
        intro _
        apply PrefixEnsures.bind (completedAllowedip_preserves initial pid ip (shape ip he))
        intro result
        apply PrefixEnsures.bind (completion_lift_same initial pid _
          (routing_kernel _ (sameKernel_branch _ _)))
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
        apply PrefixEnsures.bind (completion_lift_same initial pid _
          (routing_kernel _ (sameKernel_branch _ _)))
        intro _
        exact hn ret
  · exact hn 0

end Leanux.Proofs.WG.Configuration
