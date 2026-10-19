import SourceAip
import SourceAccess

namespace Binary.Source.Allowedips
open Leanux Leanux.WG
open Binary.Source.Aip

/-- The existing World presentation, used only after the real component's
device guard. Its equality with the actual split source is proved below. -/
def findNode (trie : Option NodeId) (bits key : Nat) : Leanux.M (Option NodeId) := do
  let mut node := trie
  let mut found : Option NodeId := none
  for _ in [0:130] do
    let id ← match node with
      | none => do _ ← branch .findNodeNode false; return found
      | some id => do _ ← branch .findNodeNode true; pure id
    let n ← Source.getNode id
    if !(← branch .findNodePrefixMatches (← WG.prefixMatches n key bits)) then return found
    if ← branch .findNodeHasPeer n.peer.isSome then found := some id
    if ← branch .findNodeFullLength (n.cidr == bits) then return found
    node ← n.bitAt (← choose n key)
  invariant "find_node deeper than MAX_ALLOWEDIPS_DEPTH"

private theorem common_corr (node : AipNode) (key bits : Nat) :
    Corresponds (WG.commonBits node key bits) (WG.commonBits node key bits) := by
  unfold WG.commonBits
  apply bind_corr (ambient_corr (AmbientM.branch .commonBits32 (bits == 32)))
  intro b
  cases b with
  | true => exact pure_corr _
  | false =>
    apply bind_corr (ambient_corr (AmbientM.branch .commonBits128 (bits == 128)))
    intro b
    cases b with
    | false => exact pure_corr _
    | true =>
      apply bind_corr (ambient_corr (AmbientM.branch .fls128High ((node.bits ^^^ key) / 2^64 != 0)))
      intro high
      cases high <;> exact pure_corr _

private theorem prefix_corr (node : AipNode) (key bits : Nat) :
    Corresponds (WG.prefixMatches node key bits) (WG.prefixMatches node key bits) := by
  unfold WG.prefixMatches
  apply bind_corr (common_corr node key bits)
  intro common
  exact pure_corr _

private theorem choose_corr (node : AipNode) (key : Nat) :
    Corresponds (choose node key) (choose node key) := by
  unfold choose
  split
  · apply bind_corr (ambient_corr (AmbientM.invariant "choose on a full-length node"))
    intro _
    exact pure_corr _
  · exact pure_corr _

private theorem bitAt_corr (node : AipNode) (bit : Nat) :
    Corresponds (node.bitAt bit) (node.bitAt bit) := by
  unfold AipNode.bitAt
  cases node.bit[bit]? with
  | none => exact ambient_corr (AmbientM.invariant _)
  | some next => exact pure_corr next

theorem findNode_corr (trie : Option NodeId) (bits key : Nat) :
    Corresponds (WG.findNode trie bits key) (findNode trie bits key) := by
  unfold WG.findNode findNode
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply bind_corr
  · apply forIn_corr
    intro i acc
    rcases acc with ⟨result, node, found⟩
    cases node with
    | none =>
      apply bind_corr (ambient_corr (AmbientM.branch .findNodeNode false))
      intro _
      exact pure_corr _
    | some id =>
      apply bind_corr (ambient_corr (AmbientM.branch .findNodeNode true))
      intro _
      apply bind_corr (pure_corr id)
      intro id
      apply bind_corr (native_corr (WG.getNode id))
      intro n
      apply bind_corr (prefix_corr n key bits)
      intro matching
      apply bind_corr (ambient_corr (AmbientM.branch .findNodePrefixMatches matching))
      intro matching
      cases matching with
      | false => exact pure_corr _
      | true =>
        apply bind_corr (ambient_corr (AmbientM.branch .findNodeHasPeer n.peer.isSome))
        intro hasPeer
        cases hasPeer <;>
          apply bind_corr (ambient_corr (AmbientM.branch .findNodeFullLength (n.cidr == bits))) <;>
          intro full
        all_goals cases full with
        | true => exact pure_corr _
        | false =>
          apply bind_corr (choose_corr n key)
          intro bit
          apply bind_corr (bitAt_corr n bit)
          intro next
          exact pure_corr _
  · intro acc
    cases acc.1 with
    | none => exact ambient_corr (AmbientM.invariant _)
    | some answer => exact pure_corr _

theorem findNode_run (trie : Option NodeId) (bits key : Nat) (w : World) (d : Device)
    (hd : w.wg.dev = some d) :
    (Source.findNode trie bits key).run w = (findNode trie bits key).run w :=
  (native_corr (WG.findNode trie bits key) w d hd).trans (findNode_corr trie bits key w d hd).symm

theorem findNode_no_device (trie : Option NodeId) (bits key : Nat) (w : World)
    (hd : w.wg.dev = none) :
    (Source.findNode trie bits key).run w =
      .error (.invariant "no WireGuard device in this trace's fixture") := by
  simp [Source.findNode, liftWG, liftAip, WG.getDev, StateT.run, bind, StateT.bind,
    get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
    invariant, AmbientM.invariant, liftM, monadLift, MonadLift.monadLift,
    StateT.lift, Except.pure, Except.bind, hd]
  rfl

def lookupBody (root : Option NodeId) (bits key : Nat) : Leanux.M (Option PeerId) := do
  Source.swapEndian bits
  let node ← Source.findNode root bits key
  if ← branch .lookupFound node.isSome then
    let some id := node | invariant "unreachable"
    let peer ← Source.peerGetMaybeZero (← Source.getNode id).peer
    if ← branch .lookupPeerGone peer.isNone then unsupported "lookup retry after a dying peer"
    return peer
  return none

theorem lookup_eq (root : Option NodeId) (bits key : Nat) :
    Source.lookup root bits key = lookupBody root bits key := by
  unfold Source.lookup WG.lookup lookupBody
  simp only [Source.liftWG_bind, Source.liftWG_branch, Source.liftWG_pure, apply_ite]
  repeat' first | rfl | (apply Source.bind_congr_right; intro x) | split
  all_goals simp_all [Source.liftWG_bind, Source.liftWG_branch, Source.liftWG_pure,
    Source.liftWG_map, Source.liftWG_unsupported, apply_ite]
  all_goals rfl

theorem swapEndian_device (bits : Nat) (w final : World) (answer : Unit)
    (accepted : (Source.swapEndian bits).run w = .ok (answer, final)) : final.wg = w.wg := by
  cases width32 : bits == 32 <;> cases width128 : bits == 128 <;>
    simp [Source.swapEndian, WG.swapEndian, liftWG, StateT.run, bind, StateT.bind,
      StateT.lift, branch, AmbientM.branch, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, pure, StateT.pure, monadLift, MonadLift.monadLift,
      Except.pure, Except.bind, width32, width128] at accepted <;>
    cases accepted <;> rfl

theorem lookup_has_device (root : Option NodeId) (bits key : Nat) (w final : World)
    (answer : Option PeerId) (accepted : (Source.lookup root bits key).run w = .ok (answer, final)) :
    ∃ d, w.wg.dev = some d := by
  cases hd : w.wg.dev with
  | some d => exact ⟨d, rfl⟩
  | none =>
    rw [lookup_eq] at accepted
    simp only [lookupBody, StateT.run_bind] at accepted
    cases hs : (Source.swapEndian bits).run w with
    | error e => simp [hs] at accepted; cases accepted
    | ok out =>
      rcases out with ⟨ignored, after⟩
      have missing : after.wg.dev = none := by rw [swapEndian_device bits w after ignored hs, hd]
      have failed := findNode_no_device root bits key after missing
      simp only [hs, Source.except_ok_bind] at accepted
      rw [failed] at accepted
      cases accepted

end Binary.Source.Allowedips
