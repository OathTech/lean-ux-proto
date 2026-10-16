import Leanux.Proofs.WG.AllowedIps.RoutingRetains
import Leanux.Proofs.WG.AllowedIps.ConfigurationInputs
import Leanux.Proofs.Logged.PrefixLoops
import Leanux.Proofs.Logged.WGPrefix

/-! Completed whole setAllowedip, removeByPeer and free calls, including attribute
guard rejection and normal allocation refusals. The explicit call sum carries
actual views and signed attribute returns; semantic validity
is proved separately from unconditional erasure. No event or native state is returned
for a primitive which Stops, while earlier completed events remain available. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
set_option pp.structureInstances false

inductive RoutingCompletedCall where
  | allowedIp (pid : PeerId) (attrs : AllowedIpAttrs) (result : Int)
  | removePeer (pid : PeerId)
  | clear

structure RoutingCompletion where
  call : RoutingCompletedCall
  before : Option RoutingState
  after : Option RoutingState

def RoutingCompletion.flat (e : RoutingCompletion) (xs : FlatTable × FlatTable) :=
  match e.call with
  | .allowedIp pid attrs result =>
    (RoutingCall.insert (attrs.family.getD 0 == AF_INET)
      (attrs.addr.getD 0) (attrs.cidr.getD 0) pid result).flat xs
  | .removePeer pid => (RoutingCall.remove pid).flat xs
  | .clear => ([], [])

def completionFold (h : List RoutingCompletion) (xs : FlatTable × FlatTable) :=
  h.foldl (fun tables e => e.flat tables) xs

@[simp] theorem completionFold_append (h k : List RoutingCompletion) (xs : FlatTable × FlatTable) :
    completionFold (h ++ k) xs = completionFold k (completionFold h xs) :=
  List.foldl_append

/-- The source witness is about the whole selected primitive, never a fabricated
insertion on guard rejection or whole peer-object removal. Flat agreement is a semantic obligation, not a
field supplied by the executable event constructor. -/
def RoutingCompletion.Valid (xs : FlatTable × FlatTable) (e : RoutingCompletion) : Prop :=
  match e.call with
  | .allowedIp pid attrs result =>
    AddressShape attrs ∧ RoutedView e.before xs ∧ RoutedView e.after (e.flat xs) ∧
    ∃ w ambient v ambient', routingView w = e.before ∧ routingView v = e.after ∧
      ((setAllowedip pid attrs).run w).run ambient = .ok ((result, v), ambient')
  | .removePeer pid =>
    RoutedView e.before xs ∧ RoutedView e.after (e.flat xs) ∧
    ∃ w ambient v ambient', routingView w = e.before ∧ routingView v = e.after ∧
      ((removeByPeer pid).run w).run ambient = .ok (((), v), ambient')
  | .clear =>
    RoutedView e.before xs ∧ RoutedView e.after (e.flat xs) ∧
    ∃ w ambient v ambient', routingView w = e.before ∧ routingView v = e.after ∧
      (WG.free.run w).run ambient = .ok (((), v), ambient')

inductive CompletionSafe (initial : FlatTable × FlatTable) : List RoutingCompletion → Prop where
  | nil : CompletionSafe initial []
  | snoc : CompletionSafe initial h → e.Valid (completionFold h initial) →
      CompletionSafe initial (h ++ [e])

def CompletionState (initial : FlatTable × FlatTable) (h : List RoutingCompletion) (w : WGWorld) : Prop :=
  CompletionSafe initial h ∧ RoutedView (routingView w) (completionFold h initial)

/-- The completed journal denotes empty tables, while the physical node store
may retain unreachable entries. This is useful before later device destruction. -/
def CompletionEmpty (initial : FlatTable × FlatTable) (h : List RoutingCompletion) (w : WGWorld) : Prop :=
  CompletionState initial h w ∧ completionFold h initial = ([], [])

def CompletionTarget (initial : FlatTable × FlatTable) (pid : PeerId)
    (h : List RoutingCompletion) (w : WGWorld) : Prop :=
  CompletionState initial h w ∧ RoutingResident pid (routingView w)

theorem setAllowedip_routed_target (pid : PeerId) (ip : AllowedIpAttrs) (hs : AddressShape ip)
    (hi : RoutedView (routingView w) xs) (hp : RoutingResident pid (routingView w))
    (hr : ((setAllowedip pid ip).run w).run ambient = .ok ((ret, v), ambient')) :
    RoutedView (routingView v)
      ((RoutingCall.insert (ip.family.getD 0 == AF_INET) (ip.addr.getD 0) (ip.cidr.getD 0) pid ret).flat xs) ∧
      RoutingResident pid (routingView v) := by
  obtain ⟨d, t4, t6, hd, hinv, h4, h6⟩ := hi.realize
  obtain ⟨p, hpid⟩ := hp.realize hd
  rcases setAllowedip_outcome pid ip hs w v ambient ambient' ret hr with ⟨rfl, hk⟩ | ⟨v4, cut, cutAmbient, hk, hf, ha, hc, hrun⟩
  · have hv : routingView v = routingView w := congrArg (fun k : WGStoreView => k.dev.map routingState) hk
    simpa [RoutingCall.flat, EINVAL, hv] using And.intro hi hp
  · have hcut : cut.dev = some d := (congrArg WGStoreView.dev hk).trans hd
    have hb : (ip.family.getD 0 == AF_INET) = v4 := by
      rw [hf]; cases v4 <;> decide
    have step : RoutingStep cut cutAmbient (.insert v4 (ip.addr.getD 0) (ip.cidr.getD 0) pid ret) v ambient' :=
      .insert ha hc ⟨d, p, hcut, hpid⟩ hrun
    obtain ⟨out, u4, u6, hout, ho, he4, he6⟩ := step.refines hcut hinv h4 h6
    refine ⟨?_, ?_⟩
    · rw [hb]
      exact ⟨out, u4, u6, by simp [routingView, hout], ho, he4, he6⟩
    · have hbool : ((if v4 then 4 else 6 : Nat) == 4) = v4 := by cases v4 <;> rfl
      obtain ⟨out', hk', ho'⟩ := insert_routing_outcome cut v cutAmbient ambient' d hcut
        (if v4 then 4 else 6) (ip.addr.getD 0) (ip.cidr.getD 0) pid p hpid t4 t6 hinv
        (by simpa only [hbool] using ha) (by simpa only [hbool] using hc) ret hrun
      have hd' : v.dev = some out' := by rw [hk']
      rcases ho'.result with ⟨_, inserted, _⟩ | ⟨_, refused⟩
      · apply routingResident_of_peer hd'
        rw [inserted.peers]
        change (d.peers[pid]?).map _ = some _
        rw [hpid]; rfl
      · exact routingResident_of_peer hd' ((refused.peers pid).trans hpid)

def completedAllowedip (pid : PeerId) (ip : AllowedIpAttrs) : WGPrefix RoutingCompletion Int :=
  fun w ambient => ExceptT.mk fun h =>
    match ((setAllowedip pid ip).run w).run ambient with
    | .error e => (.error e, h)
    | .ok ((ret, v), ambient') =>
      (.ok ((ret, v), ambient'), h ++ [⟨.allowedIp pid ip ret, routingView w, routingView v⟩])

theorem completedAllowedip_run (pid : PeerId) (ip : AllowedIpAttrs) (w : WGWorld) (ambient : Ambient) (h : List RoutingCompletion) :
    runWGPrefix (completedAllowedip pid ip) w ambient h =
      match ((setAllowedip pid ip).run w).run ambient with
      | .error e => (.error e, h)
      | .ok ((ret, v), ambient') => (.ok ((ret, v), ambient'), h ++ [⟨.allowedIp pid ip ret, routingView w, routingView v⟩]) := rfl

theorem completedAllowedip_erases (pid : PeerId) (ip : AllowedIpAttrs) :
    ErasesStatePrefix (completedAllowedip pid ip) (setAllowedip pid ip) := by
  intro w ambient h
  have hrun := completedAllowedip_run pid ip w ambient h
  dsimp only [runWGPrefix, runStatePrefix] at hrun
  rw [hrun]
  cases hr : ((setAllowedip pid ip).run w).run ambient <;> rfl

theorem completedAllowedip_preserves (initial : FlatTable × FlatTable)
    (pid : PeerId) (ip : AllowedIpAttrs) (hs : AddressShape ip) :
    StatePrefixPreserves (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (completedAllowedip pid ip) := by
  intro w ambient h hi
  have hrun := completedAllowedip_run pid ip w ambient h
  dsimp only [runWGPrefix, runStatePrefix] at hrun
  rw [hrun]
  cases hr : ((setAllowedip pid ip).run w).run ambient with
  | error err =>
    exact ⟨[], by simp, hi.1.1, trivial⟩
  | ok out =>
    obtain ⟨⟨ret, v⟩, ambient'⟩ := out
    let e : RoutingCompletion := ⟨.allowedIp pid ip ret, routingView w, routingView v⟩
    have hout := setAllowedip_routed_target pid ip hs hi.1.2 hi.2 hr
    have hv : e.Valid (completionFold h initial) := ⟨hs, hi.1.2, hout.1, w, ambient, v, ambient', rfl, rfl, hr⟩
    have safe := CompletionSafe.snoc hi.1.1 hv
    refine ⟨[e], ?_, ?_, ?_⟩
    · rfl
    · exact safe
    · change CompletionTarget initial pid (h ++ [e]) v
      refine ⟨⟨safe, ?_⟩, hout.2⟩
      simpa [completionFold, List.foldl_append, e, RoutingCompletion.flat] using hout.1

theorem completion_lift_retains {S : Type} (project : S → WGWorld)
    (initial : FlatTable × FlatTable) (a : StateT S (Except Stop) α)
    (ha : ProjectedRetainsRoutingCall project a) :
    PrefixPreserves (fun h w => CompletionState initial h (project w))
      (CompletionSafe initial) (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift
  · exact fun _ _ hi => hi.1
  · intro h w x v hi hr
    exact ⟨hi.1, hi.2.retains ((ProjectedAction.iff_run _ _ _).mp ha w x v hr)⟩

theorem completion_lift_same {S : Type} (project : S → WGWorld)
    (initial : FlatTable × FlatTable) (pid : PeerId)
    (a : StateT S (Except Stop) α)
    (ha : SameView (fun w => routingView (project w)) a) :
    PrefixEnsures (fun h w => CompletionTarget initial pid h (project w))
      (CompletionSafe initial) (liftPrefix a)
      (fun _ h w => CompletionTarget initial pid h (project w)) := by
  apply PrefixEnsures.lift
  · exact fun _ _ hi => hi.1.1
  · intro h w x v hi hr
    have he := (ProjectedAction.iff_run _ _ _).mp ha w x v hr
    simpa only [CompletionTarget, CompletionState, he] using hi

/-- Native lifts used by the WireGuard configuration callers retain both
actual execution endpoints while emitting no completion event. -/
theorem completion_lift_retains_wg (initial : FlatTable × FlatTable) (a : WG.M α)
    (ha : RetainsRoutingCall a) :
    StatePrefixPreserves (fun h w _ => CompletionState initial h w)
      (CompletionSafe initial) (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift
  · exact fun _ _ _ hi => hi.1
  · intro h w ambient x v ambient' hi hr
    exact ⟨hi.1, hi.2.retains ((ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr)⟩

theorem completion_lift_same_wg (initial : FlatTable × FlatTable) (pid : PeerId)
    (a : WG.M α) (ha : SameView routingView a) :
    StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w)
      (CompletionSafe initial) (liftWGPrefix a)
      (fun _ h w _ => CompletionTarget initial pid h w) := by
  apply StatePrefixEnsures.lift
  · exact fun _ _ _ hi => hi.1.1
  · intro h w ambient x v ambient' hi hr
    have he := (ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr
    simpa only [CompletionTarget, CompletionState, he] using hi

theorem removeByPeer_routed (pid : PeerId)
    (hi : RoutedView (routingView w) xs)
    (hr : ((removeByPeer pid).run w).run ambient = .ok (((), v), ambient')) :
    RoutedView (routingView v) ((RoutingCall.remove pid).flat xs) ∧
      RoutingResident pid (routingView v) := by
  obtain ⟨d, t4, t6, hd, hinv, h4, h6⟩ := hi.realize
  have step : RoutingStep w ambient (.remove pid) v ambient' := .remove hr
  obtain ⟨out, u4, u6, hout, ho, he4, he6⟩ := step.refines hd hinv h4 h6
  refine ⟨⟨out, u4, u6, by simp [routingView, hout], ho, he4, he6⟩, ?_⟩
  obtain ⟨p, hp⟩ := removeByPeer_input_resident w v ambient ambient' d pid hd hr
  obtain ⟨out', hk, hm⟩ := removeByPeer_endpoint w v ambient ambient' d hd pid p hp t4 t6 hinv.forest
    hinv.nodup4 hinv.nodup6 hinv.compressed4 hinv.compressed6 hinv.lists hr
  exact routingResident_of_peer (by rw [hk]) (hm.target_empty hp)

def completedRemovePeer (pid : PeerId) : WGPrefix RoutingCompletion Unit :=
  fun w ambient => ExceptT.mk fun h =>
    match ((removeByPeer pid).run w).run ambient with
    | .error err => (.error err, h)
    | .ok (((), v), ambient') => (.ok (((), v), ambient'), h ++ [⟨.removePeer pid, routingView w, routingView v⟩])

theorem completedRemovePeer_run (pid : PeerId) (w : WGWorld) (ambient : Ambient) (h : List RoutingCompletion) :
    runWGPrefix (completedRemovePeer pid) w ambient h =
      match ((removeByPeer pid).run w).run ambient with
      | .error err => (.error err, h)
      | .ok (((), v), ambient') => (.ok (((), v), ambient'), h ++ [⟨.removePeer pid, routingView w, routingView v⟩]) := rfl

theorem completedRemovePeer_erases (pid : PeerId) :
    ErasesStatePrefix (completedRemovePeer pid) (removeByPeer pid) := by
  intro w ambient h
  have hrun := completedRemovePeer_run pid w ambient h
  dsimp only [runWGPrefix, runStatePrefix] at hrun
  rw [hrun]
  cases hr : ((removeByPeer pid).run w).run ambient with
  | error e => rfl
  | ok out => rcases out with ⟨⟨u, v⟩, ambient'⟩; cases u; rfl

theorem completedRemovePeer_spec (initial : FlatTable × FlatTable) (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (completedRemovePeer pid) (fun _ h w _ => CompletionTarget initial pid h w) := by
  intro w ambient h hi
  have hrun := completedRemovePeer_run pid w ambient h
  dsimp only [runWGPrefix, runStatePrefix] at hrun
  rw [hrun]
  cases hr : ((removeByPeer pid).run w).run ambient with
  | error err => exact ⟨[], by simp, hi.1, trivial⟩
  | ok out =>
    obtain ⟨⟨u, v⟩, ambient'⟩ := out
    cases u
    let e : RoutingCompletion := ⟨.removePeer pid, routingView w, routingView v⟩
    have hout := removeByPeer_routed pid hi.2 hr
    have hv : e.Valid (completionFold h initial) := ⟨hi.2, hout.1, w, ambient, v, ambient', rfl, rfl, hr⟩
    have safe := CompletionSafe.snoc hi.1 hv
    refine ⟨[e], rfl, safe, ⟨⟨safe, ?_⟩, hout.2⟩⟩
    simpa [completionFold, List.foldl_append, e, RoutingCompletion.flat] using hout.1


/-- Only a normal original free emits a completed clear; a failed traversal can
have performed effects, but its unavailable native state is not invented here. -/
def completedFree : WGPrefix RoutingCompletion Unit :=
  fun w ambient => ExceptT.mk fun h =>
    match (WG.free.run w).run ambient with
    | .error err => (.error err, h)
    | .ok (((), v), ambient') => (.ok (((), v), ambient'), h ++ [⟨.clear, routingView w, routingView v⟩])

theorem completedFree_run (w : WGWorld) (ambient : Ambient) (h : List RoutingCompletion) :
    runWGPrefix completedFree w ambient h =
      match (WG.free.run w).run ambient with
      | .error err => (.error err, h)
      | .ok (((), v), ambient') => (.ok (((), v), ambient'), h ++ [⟨.clear, routingView w, routingView v⟩]) := rfl

theorem completedFree_erases : ErasesStatePrefix completedFree WG.free := by
  intro w ambient h
  have hrun := completedFree_run w ambient h
  dsimp only [runWGPrefix, runStatePrefix] at hrun
  rw [hrun]
  cases hr : (WG.free.run w).run ambient with
  | error e => rfl
  | ok out => rcases out with ⟨⟨u, v⟩, ambient'⟩; cases u; rfl

theorem completedFree_empty_spec (initial : FlatTable × FlatTable) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      completedFree (fun _ h w _ => CompletionEmpty initial h w) := by
  intro w ambient h hi
  have hrun := completedFree_run w ambient h
  dsimp only [runWGPrefix, runStatePrefix] at hrun
  rw [hrun]
  cases hr : (WG.free.run w).run ambient with
  | error err => exact ⟨[], by simp, hi.1, trivial⟩
  | ok out =>
    obtain ⟨⟨u, v⟩, ambient'⟩ := out
    cases u
    obtain ⟨d, t4, t6, hd, hinv, h4, h6⟩ := hi.2.realize
    have step : RoutingStep w ambient .clear v ambient' := .clear hr
    obtain ⟨out, u4, u6, hout, ho, he4, he6⟩ := step.refines hd hinv h4 h6
    let e : RoutingCompletion := ⟨.clear, routingView w, routingView v⟩
    have routed : RoutedView (routingView v) ([], []) :=
      ⟨out, u4, u6, by simp [routingView, hout], ho, he4, he6⟩
    have hv : e.Valid (completionFold h initial) := ⟨hi.2, routed, w, ambient, v, ambient', rfl, rfl, hr⟩
    have safe := CompletionSafe.snoc hi.1 hv
    refine ⟨[e], rfl, safe, ⟨⟨safe, ?_⟩, ?_⟩⟩
    · simpa [completionFold, List.foldl_append, e, RoutingCompletion.flat] using routed
    · simp [completionFold, List.foldl_append, e, RoutingCompletion.flat]

theorem completedFree_spec (initial : FlatTable × FlatTable) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      completedFree (fun _ h w _ => CompletionState initial h w) :=
  (completedFree_empty_spec initial).consequence (fun _ _ _ h => h) (fun _ _ _ _ h => h.1)

theorem completion_empty_lift {S : Type} (project : S → WGWorld)
    (initial : FlatTable × FlatTable) (a : StateT S (Except Stop) α)
    (ha : ProjectedRetainsRoutingCall project a) :
    PrefixPreserves (fun h w => CompletionEmpty initial h (project w))
      (CompletionSafe initial) (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.1)
  intro h w x v hi hr
  exact ⟨⟨hi.1.1, hi.1.2.retains ((ProjectedAction.iff_run _ _ _).mp ha w x v hr)⟩, hi.2⟩

theorem completion_empty_lift_wg (initial : FlatTable × FlatTable) (a : WG.M α)
    (ha : RetainsRoutingCall a) :
    StatePrefixPreserves (fun h w _ => CompletionEmpty initial h w)
      (CompletionSafe initial) (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.1)
  intro h w ambient x v ambient' hi hr
  exact ⟨⟨hi.1.1, hi.1.2.retains ((ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr)⟩, hi.2⟩

theorem completedRemovePeer_empty_spec (initial : FlatTable × FlatTable) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => CompletionEmpty initial h w) (CompletionSafe initial) (completedRemovePeer pid) := by
  intro w ambient h hi
  have hs := completedRemovePeer_spec initial pid w ambient h hi.1
  have hrun := completedRemovePeer_run pid w ambient h
  dsimp only [runWGPrefix, runStatePrefix] at hrun
  rw [hrun] at hs ⊢
  cases hr : ((removeByPeer pid).run w).run ambient with
  | error err => simpa only [hr] using hs
  | ok out =>
    obtain ⟨⟨u, v⟩, ambient'⟩ := out
    cases u
    simp only [hr] at hs ⊢
    obtain ⟨suffix, he, safe, post⟩ := hs
    refine ⟨suffix, he, safe, ⟨post.1, ?_⟩⟩
    rw [completionFold_append, hi.2]
    rfl

end Leanux.Proofs.WG.AllowedIps
