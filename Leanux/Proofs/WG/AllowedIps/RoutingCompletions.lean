import Leanux.Proofs.WG.AllowedIps.RoutingRetains
import Leanux.Proofs.WG.AllowedIps.ConfigurationInputs
import Leanux.Proofs.Logged.PrefixLoops

/-! Completed whole setAllowedip and removeByPeer calls, including attribute
guard rejection and normal allocation refusals. The explicit call sum carries
actual views and signed attribute returns; semantic validity
is proved separately from unconditional erasure. No event or World is returned
for a primitive which Stops, while earlier completed events remain available. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
set_option pp.structureInstances false

inductive RoutingCompletedCall where
  | allowedIp (pid : PeerId) (attrs : AllowedIpAttrs) (result : Int)
  | removePeer (pid : PeerId)

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
    ∃ w v, routingView w = e.before ∧ routingView v = e.after ∧
      (setAllowedip pid attrs).run w = .ok (result, v)
  | .removePeer pid =>
    RoutedView e.before xs ∧ RoutedView e.after (e.flat xs) ∧
    ∃ w v, routingView w = e.before ∧ routingView v = e.after ∧
      (removeByPeer pid).run w = .ok ((), v)

inductive CompletionSafe (initial : FlatTable × FlatTable) : List RoutingCompletion → Prop where
  | nil : CompletionSafe initial []
  | snoc : CompletionSafe initial h → e.Valid (completionFold h initial) →
      CompletionSafe initial (h ++ [e])

def CompletionState (initial : FlatTable × FlatTable) (h : List RoutingCompletion) (w : World) : Prop :=
  CompletionSafe initial h ∧ RoutedView (routingView w) (completionFold h initial)

def CompletionTarget (initial : FlatTable × FlatTable) (pid : PeerId)
    (h : List RoutingCompletion) (w : World) : Prop :=
  CompletionState initial h w ∧ RoutingResident pid (routingView w)

theorem setAllowedip_routed_target (pid : PeerId) (ip : AllowedIpAttrs) (hs : AddressShape ip)
    (hi : RoutedView (routingView w) xs) (hp : RoutingResident pid (routingView w))
    (hr : (setAllowedip pid ip).run w = .ok (ret, v)) :
    RoutedView (routingView v)
      ((RoutingCall.insert (ip.family.getD 0 == AF_INET) (ip.addr.getD 0) (ip.cidr.getD 0) pid ret).flat xs) ∧
      RoutingResident pid (routingView v) := by
  obtain ⟨d, t4, t6, hd, hinv, h4, h6⟩ := hi.realize
  obtain ⟨p, hpid⟩ := hp.realize hd
  rcases setAllowedip_outcome pid ip hs w v ret hr with ⟨rfl, hk⟩ | ⟨v4, cut, hk, hf, ha, hc, hrun⟩
  · have hv : routingView v = routingView w := congrArg (fun k => k.wg.map routingState) hk
    simpa [RoutingCall.flat, EINVAL, hv] using And.intro hi hp
  · have hcut : cut.k.wg = some d := by rw [hk, hd]
    have hb : (ip.family.getD 0 == AF_INET) = v4 := by
      rw [hf]; cases v4 <;> decide
    have step : RoutingStep cut (.insert v4 (ip.addr.getD 0) (ip.cidr.getD 0) pid ret) v :=
      .insert ha hc ⟨d, p, hcut, hpid⟩ hrun
    obtain ⟨out, u4, u6, hout, ho, he4, he6⟩ := step.refines hcut hinv h4 h6
    refine ⟨?_, ?_⟩
    · rw [hb]
      exact ⟨out, u4, u6, by simp [routingView, hout], ho, he4, he6⟩
    · have hbool : ((if v4 then 4 else 6 : Nat) == 4) = v4 := by cases v4 <;> rfl
      obtain ⟨out', hk', ho'⟩ := insert_routing_outcome cut v d hcut
        (if v4 then 4 else 6) (ip.addr.getD 0) (ip.cidr.getD 0) pid p hpid t4 t6 hinv
        (by simpa only [hbool] using ha) (by simpa only [hbool] using hc) ret hrun
      have hd' : v.k.wg = some out' := by rw [hk']
      rcases ho'.result with ⟨_, inserted, _⟩ | ⟨_, refused⟩
      · apply routingResident_of_peer hd'
        rw [inserted.peers]
        change (d.peers[pid]?).map _ = some _
        rw [hpid]; rfl
      · exact routingResident_of_peer hd' ((refused.peers pid).trans hpid)

def completedAllowedip (pid : PeerId) (ip : AllowedIpAttrs) : PrefixM RoutingCompletion Int :=
  fun w => ExceptT.mk fun h =>
    match (setAllowedip pid ip).run w with
    | .error e => (.error e, h)
    | .ok (ret, v) =>
      (.ok (ret, v), h ++ [⟨.allowedIp pid ip ret, routingView w, routingView v⟩])

theorem completedAllowedip_run (pid : PeerId) (ip : AllowedIpAttrs) (w : World) (h : List RoutingCompletion) :
    runPrefix (completedAllowedip pid ip) w h =
      match (setAllowedip pid ip).run w with
      | .error e => (.error e, h)
      | .ok (ret, v) => (.ok (ret, v), h ++ [⟨.allowedIp pid ip ret, routingView w, routingView v⟩]) := rfl

theorem completedAllowedip_erases (pid : PeerId) (ip : AllowedIpAttrs) :
    ErasesPrefix (completedAllowedip pid ip) (setAllowedip pid ip) := by
  intro w h
  rw [completedAllowedip_run]
  cases hr : (setAllowedip pid ip).run w <;> rfl

theorem completedAllowedip_preserves (initial : FlatTable × FlatTable)
    (pid : PeerId) (ip : AllowedIpAttrs) (hs : AddressShape ip) :
    PrefixPreserves (CompletionTarget initial pid) (CompletionSafe initial)
      (completedAllowedip pid ip) := by
  intro w h hi
  simp only [completedAllowedip_run]
  cases hr : (setAllowedip pid ip).run w with
  | error err =>
    exact ⟨[], by simp, hi.1.1, trivial⟩
  | ok out =>
    obtain ⟨ret, v⟩ := out
    let e : RoutingCompletion := ⟨.allowedIp pid ip ret, routingView w, routingView v⟩
    have hout := setAllowedip_routed_target pid ip hs hi.1.2 hi.2 hr
    have hv : e.Valid (completionFold h initial) := ⟨hs, hi.1.2, hout.1, w, v, rfl, rfl, hr⟩
    have safe := CompletionSafe.snoc hi.1.1 hv
    refine ⟨[e], ?_, ?_, ?_⟩
    · rfl
    · exact safe
    · change CompletionTarget initial pid (h ++ [e]) v
      refine ⟨⟨safe, ?_⟩, hout.2⟩
      simpa [completionFold, List.foldl_append, e, RoutingCompletion.flat] using hout.1

theorem completion_lift_retains (initial : FlatTable × FlatTable) (a : M α)
    (ha : RetainsRoutingCall a) :
    PrefixPreserves (CompletionState initial) (CompletionSafe initial) (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift
  · exact fun _ _ hi => hi.1
  · intro h w x v hi hr
    exact ⟨hi.1, hi.2.retains (ha w x v hr)⟩

theorem completion_lift_same (initial : FlatTable × FlatTable) (pid : PeerId)
    (a : M α) (ha : SameView routingView a) :
    PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial) (liftPrefix a)
      (fun _ => CompletionTarget initial pid) := by
  apply PrefixEnsures.lift
  · exact fun _ _ hi => hi.1.1
  · intro h w x v hi hr
    simpa only [CompletionTarget, CompletionState, ha w x v hr] using hi

theorem removeByPeer_routed (pid : PeerId)
    (hi : RoutedView (routingView w) xs)
    (hr : (removeByPeer pid).run w = .ok ((), v)) :
    RoutedView (routingView v) ((RoutingCall.remove pid).flat xs) ∧
      RoutingResident pid (routingView v) := by
  obtain ⟨d, t4, t6, hd, hinv, h4, h6⟩ := hi.realize
  have step : RoutingStep w (.remove pid) v := .remove hr
  obtain ⟨out, u4, u6, hout, ho, he4, he6⟩ := step.refines hd hinv h4 h6
  refine ⟨⟨out, u4, u6, by simp [routingView, hout], ho, he4, he6⟩, ?_⟩
  obtain ⟨p, hp⟩ := removeByPeer_input_resident w v d pid hd hr
  obtain ⟨out', hk, hm⟩ := removeByPeer_endpoint w v d hd pid p hp t4 t6 hinv.forest
    hinv.nodup4 hinv.nodup6 hinv.compressed4 hinv.compressed6 hinv.lists hr
  exact routingResident_of_peer (by rw [hk]) (hm.target_empty hp)

def completedRemovePeer (pid : PeerId) : PrefixM RoutingCompletion Unit :=
  fun w => ExceptT.mk fun h =>
    match (removeByPeer pid).run w with
    | .error err => (.error err, h)
    | .ok ((), v) => (.ok ((), v), h ++ [⟨.removePeer pid, routingView w, routingView v⟩])

theorem completedRemovePeer_run (pid : PeerId) (w : World) (h : List RoutingCompletion) :
    runPrefix (completedRemovePeer pid) w h =
      match (removeByPeer pid).run w with
      | .error err => (.error err, h)
      | .ok ((), v) => (.ok ((), v), h ++ [⟨.removePeer pid, routingView w, routingView v⟩]) := rfl

theorem completedRemovePeer_erases (pid : PeerId) :
    ErasesPrefix (completedRemovePeer pid) (removeByPeer pid) := by
  intro w h
  rw [completedRemovePeer_run]
  cases hr : (removeByPeer pid).run w with
  | error e => rfl
  | ok out => cases out with | mk u v => cases u; rfl

theorem completedRemovePeer_spec (initial : FlatTable × FlatTable) (pid : PeerId) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (completedRemovePeer pid) (fun _ => CompletionTarget initial pid) := by
  intro w h hi
  rw [completedRemovePeer_run]
  cases hr : (removeByPeer pid).run w with
  | error err => exact ⟨[], by simp, hi.1, trivial⟩
  | ok out =>
    obtain ⟨u, v⟩ := out
    cases u
    let e : RoutingCompletion := ⟨.removePeer pid, routingView w, routingView v⟩
    have hout := removeByPeer_routed pid hi.2 hr
    have hv : e.Valid (completionFold h initial) := ⟨hi.2, hout.1, w, v, rfl, rfl, hr⟩
    have safe := CompletionSafe.snoc hi.1 hv
    refine ⟨[e], rfl, safe, ⟨⟨safe, ?_⟩, hout.2⟩⟩
    simpa [completionFold, List.foldl_append, e, RoutingCompletion.flat] using hout.1

end Leanux.Proofs.WG.AllowedIps
