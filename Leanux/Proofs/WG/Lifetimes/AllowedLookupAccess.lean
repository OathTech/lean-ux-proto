import Leanux.Proofs.WG.Lifetimes.TxStagingCalls

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Allowed-IP lookups observe peer reference acquisition after the original
node search. Node and scalar accesses are outside the three lifetime stores.
No represented-trie or successful-search premise is imposed. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem swapEndian_sameKernel (bits : Nat) : SameKernel (swapEndian bits) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [swapEndian, branch, invariant, unsupported]

theorem getNode_sameKernel (id : NodeId) : SameKernel (getNode id) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [getNode, getDev, getK, invariant]

theorem findNode_sameKernel (root : Option NodeId) (bits key : Nat) :
    SameKernel (findNode root bits key) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [findNode, getNode, getDev, getK, prefixMatches, commonBits, choose,
    AipNode.bitAt, branch, invariant, unsupported]
  invariants
  | inv1 => ((⇓? _ w => ⌜w.k = k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all

def lookupPrefix (root : Option NodeId) (bits key : Nat) : MixedM (Option PeerId) := do
  liftPrefix (swapEndian bits)
  let node ← liftPrefix (findNode root bits key)
  if ← liftPrefix (branch .lookupFound node.isSome) then
    let some id := node | liftPrefix (invariant "unreachable")
    let peer ← peerGetMaybeZeroPrefix (← liftPrefix (getNode id)).peer
    if ← liftPrefix (branch .lookupPeerGone peer.isNone) then
      liftPrefix (unsupported "lookup retry after a dying peer")
    return peer
  return none

def lookupSrcPrefix (protocol : Nat) (bytes : List UInt8) : MixedM (Option PeerId) := do
  let t := (← liftPrefix getDev).peerAllowedips
  if ← liftPrefix (branch .lookupSrcV4 (protocol == 4)) then return ← lookupPrefix t.root4 32 (beAt bytes 12 4)
  if ← liftPrefix (branch .lookupSrcV6 (protocol == 6)) then return ← lookupPrefix t.root6 128 (beAt bytes 8 16)
  return none

def lookupDstPrefix (family addr : Nat) : MixedM (Option PeerId) := do
  let t := (← liftPrefix getDev).peerAllowedips
  if ← liftPrefix (branch .lookupDstV4 (family == 4)) then return ← lookupPrefix t.root4 32 addr
  if ← liftPrefix (branch .lookupDstV6 (family == 6)) then return ← lookupPrefix t.root6 128 addr
  return none

theorem lookupPrefix_erases (root : Option NodeId) (bits key : Nat) :
    ErasesPrefix (lookupPrefix root bits key) (lookup root bits key) := by
  unfold lookupPrefix lookup
  repeat' first
    | with_reducible exact peerGetMaybeZeroPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | split
    | (solve | simp_all)
    | (with_reducible intro x; try dsimp only)

  all_goals simp_all only [Option.some.injEq]
  all_goals exact erasesPrefix_lift _

theorem lookupPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (root : Option NodeId) (bits key : Nat) :
    AmbientSpec I P (lookupPrefix root bits key) (fun _ => P) := by
  unfold lookupPrefix
  repeat' first
    | exact peerGetMaybeZeroPrefix_spec_ambient c P _
    | exact c.kernel P _ (swapEndian_sameKernel _)
    | exact c.kernel P _ (findNode_sameKernel _ _ _)
    | exact c.kernel P _ (getNode_sameKernel _)
    | exact c.branch P _ _
    | exact c.invariant P _
    | exact c.unsupported P _
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem lookupSrcPrefix_erases (protocol : Nat) (bytes : List UInt8) :
    ErasesPrefix (lookupSrcPrefix protocol bytes) (lookupSrc protocol bytes) := by
  unfold lookupSrcPrefix lookupSrc
  repeat' first
    | exact lookupPrefix_erases _ _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | split
    | (intro x; try dsimp only)

theorem lookupSrcPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (protocol : Nat) (bytes : List UInt8) : AmbientSpec I P (lookupSrcPrefix protocol bytes) (fun _ => P) := by
  unfold lookupSrcPrefix
  repeat' first
    | exact lookupPrefix_spec c P _ _ _
    | exact c.kernel P _ getDev_sameKernel
    | exact c.branch P _ _
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem lookupDstPrefix_erases (family addr : Nat) :
    ErasesPrefix (lookupDstPrefix family addr) (lookupDst family addr) := by
  unfold lookupDstPrefix lookupDst
  repeat' first
    | exact lookupPrefix_erases _ _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | split
    | (intro x; try dsimp only)

theorem lookupDstPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (family addr : Nat) : AmbientSpec I P (lookupDstPrefix family addr) (fun _ => P) := by
  unfold lookupDstPrefix
  repeat' first
    | exact lookupPrefix_spec c P _ _ _
    | exact c.kernel P _ getDev_sameKernel
    | exact c.branch P _ _
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
