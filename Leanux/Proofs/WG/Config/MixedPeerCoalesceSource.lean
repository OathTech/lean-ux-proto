import Leanux.Proofs.WG.Config.MixedPeerCoalesceModel
import Leanux.Proofs.WG.Config.TwoPageCoalesceSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The actual first-peer step merges only the continuation array, preserving
all preceding records and fixed attributes. No distinct-key premise is needed. -/
theorem coalescePeerStep_continuation (prior : Array PeerDumpAttrs) (key : String)
    (fixed : List (String × Json)) (before more : Array Json) (split : Bool)
    (canonical : ∀ item ∈ fixed, item.1 ≠ "allowed_ips") :
    coalescePeerStep (coalesceAipPart key [("public_key",toJson key)] more split)
      (prior.push (coalesceAipPart key fixed before true),true) =
      (pure (.yield (prior.push (coalesceAipPart key fixed (before ++ more) split),false)) : WG.M _) := by
  have kept : fixed.map (fun item => if item.1 = "allowed_ips" then
      (item.1,match item.2 with | Json.arr a => Json.arr (a ++ more) | v => v) else (item.1,item.2)) = fixed := by
    induction fixed with
    | nil => rfl
    | cons item rest ih =>
      have first := canonical item (by simp)
      have later : ∀ q ∈ rest, q.1 ≠ "allowed_ips" := fun q member => canonical q (by simp [member])
      simp only [List.map_cons,ite_eq_right first,ih later]
  simp [coalescePeerStep,coalesceAipPart,List.lookup]
  exact congrArg (fun attrs : List (String × Json) =>
    (pure (ForInStep.yield (prior.push (PeerDumpAttrs.mk key
      (attrs ++ [("allowed_ips",Json.arr (before ++ more))]) split),false)) :
      WG.M (ForInStep (Array PeerDumpAttrs × Bool)))) kept

/-- Only the first item can continue the previous page. Every following item
is appended with the original missing-allowed_ips normalization, even if its
public key repeats the continued key or any earlier key. -/
theorem coalescePeers_continuation_front (prior : Array PeerDumpAttrs) (key : String)
    (fixed : List (String × Json)) (before more : Array Json) (split : Bool)
    (following : List PeerDumpAttrs)
    (canonical : ∀ item ∈ fixed, item.1 ≠ "allowed_ips") :
    forIn (coalesceAipPart key [("public_key",toJson key)] more split :: following)
      (prior.push (coalesceAipPart key fixed before true),true) coalescePeerStep =
      (pure (prior.push (coalesceAipPart key fixed (before ++ more) split) ++
        (following.map peerDumpWithIps).toArray,false) : WG.M _) := by
  rw [List.forIn_cons,coalescePeerStep_continuation prior key fixed before more split canonical]
  simpa using coalescePeers_afterFirst following
    (prior.push (coalesceAipPart key fixed (before ++ more) split))

/-- Two adjacent DATA pages merge a continued boundary peer and append every
following peer record. The second header may be absent or exactly repeat the
first device attributes, as the actual callbacks require. The preceding records
and remaining messages are arbitrary, including later errors. This proves no
producer behavior. -/
theorem coalesce_mixed_pages_merge (d : Device) (preceding following : List PeerDumpAttrs)
    (key : String) (fixed : List (String × Json)) (before more : Array Json)
    (split : Bool) (secondPart : List (String × Json)) (tail : List NlMessage)
    (canonical : ∀ item ∈ fixed, item.1 ≠ "allowed_ips")
    (header : secondPart = [] ∨ secondPart = deviceFixedAttrs d) :
    coalesce (.data 2 (deviceFixedAttrs d)
      (some (preceding ++ [coalesceAipPart key fixed before true])) ::
      .data 2 secondPart (some (coalesceAipPart key [("public_key",toJson key)] more split :: following)) :: tail) =
    coalesce (.data 2 (deviceFixedAttrs d)
      (some (preceding ++ coalesceAipPart key fixed (before ++ more) split :: following)) :: tail) := by
  have nonempty : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  let firstPage := preceding ++ [coalesceAipPart key fixed before true]
  let nextPage := coalesceAipPart key [("public_key",toJson key)] more split :: following
  let mergedPage := preceding ++ coalesceAipPart key fixed (before ++ more) split :: following
  have normalized (ips : Array Json) (flag : Bool) :
      peerDumpWithIps (coalesceAipPart key fixed ips flag) = coalesceAipPart key fixed ips flag := by
    simp [peerDumpWithIps,coalesceAipPart]
  have firstPeers : (firstPage.map peerDumpWithIps).toArray =
      (preceding.map peerDumpWithIps).toArray.push (coalesceAipPart key fixed before true) := by
    simp [firstPage,normalized]
  have mergedPeers : (mergedPage.map peerDumpWithIps).toArray =
      (preceding.map peerDumpWithIps).toArray.push
        (coalesceAipPart key fixed (before ++ more) split) ++
        (following.map peerDumpWithIps).toArray := by
    simp [mergedPage,normalized]
  have first := coalescePeers_complete_front #[] firstPage (Or.inl rfl)
  have second : forIn nextPage
      ((preceding.map peerDumpWithIps).toArray.push (coalesceAipPart key fixed before true),true)
      coalescePeerStep =
      (pure ((preceding.map peerDumpWithIps).toArray.push
        (coalesceAipPart key fixed (before ++ more) split) ++
        (following.map peerDumpWithIps).toArray,false) : WG.M _) :=
    coalescePeers_continuation_front _ key fixed before more split following canonical
  have together := coalescePeers_complete_front #[] mergedPage (Or.inl rfl)
  change coalesce (.data 2 (deviceFixedAttrs d) (some firstPage) ::
    .data 2 secondPart (some nextPage) :: tail) =
    coalesce (.data 2 (deviceFixedAttrs d) (some mergedPage) :: tail)
  rcases header with rfl | rfl
  all_goals
    simp [coalesce,nonempty]
    conv in (forIn firstPage _ _) =>
      arg 3
      tactic =>
        exact show _ = coalescePeerStep from by
          funext p state
          simp [coalescePeerStep,peerDumpWithIps]
          congr 3
    conv in (forIn nextPage _ _) =>
      arg 3
      tactic =>
        exact show _ = coalescePeerStep from by
          funext p state
          simp [coalescePeerStep,peerDumpWithIps]
          congr 3
    conv in (forIn mergedPage _ _) =>
      arg 3
      tactic =>
        exact show _ = coalescePeerStep from by
          funext p state
          simp [coalescePeerStep,peerDumpWithIps]
          congr 3
    rw [first]
    simp only [Array.empty_append,pure_bind,firstPeers]
    rw [second,together]
    simp only [Array.empty_append,pure_bind,mergedPeers]

end Leanux.Proofs.WG.Config
