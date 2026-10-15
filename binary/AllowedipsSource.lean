import MirrorPeerPoints
import Leanux.WG.Device
import AllowedipsSelection

namespace Binary.AllowedipsSource
open Leanux Leanux.WG MirrorHistory

/-- Operational logging of the two swap-endian choices. -/
def swapEndian (bits : Nat) : Logged Unit := do
  if ← branchLogged .swapEndian32 (bits == 32) then return
  _ ← branchLogged .swapEndian128 (bits == 128)

def commonBits (node : AipNode) (key bits : Nat) : Logged Nat := do
  if ← branchLogged .commonBits32 (bits == 32) then
    return 32 - fls (node.bits ^^^ key)
  if ← branchLogged .commonBits128 (bits == 128) then
    let x := node.bits ^^^ key
    let high := x / 2 ^ 64
    let n ← do
      if ← branchLogged .fls128High (high != 0) then pure (fls high + 64)
      else pure (fls (x % 2 ^ 64))
    return 128 - n
  return 0

def prefixMatches (node : AipNode) (key bits : Nat) : Logged Bool := do
  let common ← called "common_bits" (commonBits node key bits)
  return common ≥ node.cidr

/-- Same bounded operational loop as the mirror. Exhausting its bound still
    fails; logging does not add a successful fuel-exhaustion path. -/
def findNode (trie : Option NodeId) (bits key : Nat) : Logged (Option NodeId) := do
  let mut node := trie
  let mut found : Option NodeId := none
  for _ in [0:130] do
    let id ← match node with
      | none => do _ ← branchLogged .findNodeNode false; return found
      | some id => do _ ← branchLogged .findNodeNode true; pure id
    let n ← StateT.lift (getNode id)
    if !(← branchLogged .findNodePrefixMatches (← prefixMatches n key bits)) then return found
    if ← branchLogged .findNodeHasPeer n.peer.isSome then found := some id
    if ← branchLogged .findNodeFullLength (n.cidr == bits) then return found
    node ← StateT.lift (n.bitAt (← StateT.lift (choose n key)))
  StateT.lift (invariant "find_node deeper than MAX_ALLOWEDIPS_DEPTH")

def lookup (root : Option NodeId) (bits key : Nat) : Logged (Option PeerId) :=
  called "lookup" do
    swapEndian bits
    let node ← findNode root bits key
    if ← branchLogged .lookupFound node.isSome then
      let some id := node | StateT.lift (invariant "unreachable")
      let n ← StateT.lift (getNode id)
      let peer ← called "wg_peer_get_maybe_zero" (peerGet n.peer)
      if ← branchLogged .lookupPeerGone peer.isNone then
        StateT.lift (unsupported "lookup retry after a dying peer")
      return peer
    return none

theorem swapEndian_erases (bits : Nat) :
    Erases (swapEndian bits) (WG.swapEndian bits) := by
  unfold swapEndian WG.swapEndian
  apply erases_bind (branch_erases _ _)
  intro b
  cases b with
  | true => exact erases_pure _
  | false =>
    apply erases_bind (branch_erases _ _)
    intro _
    exact erases_pure _

theorem commonBits_erases (node : AipNode) (key bits : Nat) :
    Erases (commonBits node key bits) (WG.commonBits node key bits) := by
  unfold commonBits WG.commonBits
  apply erases_bind (branch_erases _ _)
  intro b
  cases b with
  | true => exact erases_pure _
  | false =>
    apply erases_bind (branch_erases _ _)
    intro b
    cases b with
    | false => exact erases_pure _
    | true =>
      apply erases_bind (branch_erases _ _)
      intro high
      cases high <;> exact erases_pure _

theorem prefixMatches_erases (node : AipNode) (key bits : Nat) :
    Erases (prefixMatches node key bits) (WG.prefixMatches node key bits) := by
  unfold prefixMatches WG.prefixMatches
  apply erases_bind (called_erases _ _ _ (commonBits_erases node key bits))
  intro n
  exact erases_pure _

theorem erases_forIn_range (range : Std.Legacy.Range) (b : β)
    (logged : Nat → β → Logged (ForInStep β))
    (original : Nat → β → M (ForInStep β))
    (same : ∀ i acc, Erases (logged i acc) (original i acc)) :
    Erases (forIn range b logged) (forIn range b original) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact erases_forIn _ b logged original same

theorem findNode_erases (trie : Option NodeId) (bits key : Nat) :
    Erases (findNode trie bits key) (WG.findNode trie bits key) := by
  unfold findNode WG.findNode
  apply erases_bind
  · apply erases_forIn_range
    intro i acc
    rcases acc with ⟨result, node, found⟩
    cases node with
    | none =>
      apply erases_bind (branch_erases _ _)
      intro _
      exact erases_pure _
    | some id =>
      apply erases_bind (branch_erases _ _)
      intro _
      apply erases_bind (erases_pure id)
      intro id
      apply erases_bind (erases_lift _)
      intro n
      apply erases_bind (prefixMatches_erases n key bits)
      intro matching
      apply erases_bind (branch_erases _ _)
      intro matching
      cases matching with
      | false => exact erases_pure _
      | true =>
        apply erases_bind (branch_erases _ _)
        intro hasPeer
        cases hasPeer <;>
          apply erases_bind (branch_erases _ _) <;>
          intro full
        all_goals cases full with
        | true => exact erases_pure _
        | false =>
          apply erases_bind (erases_lift _)
          intro bit
          apply erases_bind (erases_lift _)
          intro next
          exact erases_pure _
  · intro acc
    cases acc.1 with
    | none => exact erases_lift _
    | some answer => exact erases_pure _

theorem lookup_erases (root : Option NodeId) (bits key : Nat) :
    Erases (lookup root bits key) (WG.lookup root bits key) := by
  unfold lookup WG.lookup
  apply called_erases
  apply erases_bind (swapEndian_erases bits)
  intro _
  apply erases_bind (findNode_erases root bits key)
  intro node
  apply erases_bind (branch_erases _ _)
  intro found
  cases found with
  | false => exact erases_pure _
  | true =>
    cases node with
    | none =>
      apply erases_bind (erases_lift _)
      intro _
      exact erases_pure _
    | some id =>
      apply erases_bind (erases_lift _)
      intro n
      apply erases_bind (called_erases _ _ _ (peerGet_erases n.peer))
      intro peer
      apply erases_bind (branch_erases _ _)
      intro gone
      cases gone with
      | false => exact erases_pure _
      | true =>
        apply erases_bind (erases_lift _)
        intro _
        exact erases_pure _

#print axioms findNode_erases
#print axioms lookup_erases

/-- Successful source execution supplies its exact logged execution. This
    is derived from erasure, rather than an additional acceptance premise. -/
theorem accepted_logged {logged : Logged α} {original : M α}
    (same : Erases logged original) (history : List Point) (world final : World)
    (answer : α) (accepted : original.run world = .ok (answer, final)) :
    ∃ points, (logged.run history).run world = .ok ((answer, points), final) := by
  have erased := same history world
  rw [accepted] at erased
  cases actual : (logged.run history).run world with
  | error e => simp [actual, erase] at erased
  | ok value =>
    obtain ⟨⟨result, points⟩, after⟩ := value
    simp only [actual, erase, Except.ok.injEq, Prod.mk.injEq] at erased
    obtain ⟨rfl, rfl⟩ := erased
    exact ⟨points, rfl⟩

theorem lookup_accepted (root : Option NodeId) (bits key : Nat)
    (history : List Point) (world final : World) (answer : Option PeerId)
    (accepted : (WG.lookup root bits key).run world = .ok (answer, final)) :
    ∃ points, ((lookup root bits key).run history).run world = .ok ((answer, points), final) :=
  accepted_logged (lookup_erases root bits key) history world final answer accepted

abbrev Choices := List (Decision × Bool)

def records : World → Choices → World
  | w, [] => w
  | w, (d,b) :: rest => records (LookupMirror.record w d b) rest

/-- Every choice point contains the actual cumulative source world, after
    recording its decision. Calls and returns are added by `called`. -/
def choicePoints : World → Choices → List Point
  | _, [] => []
  | w, (d,b) :: rest =>
    let next := LookupMirror.record w d b
    ⟨.decision d, next⟩ :: choicePoints next rest

def commonChoices (node : AipNode) (key bits : Nat) : Choices :=
  if bits == 32 then [(.commonBits32,true)]
  else if bits == 128 then
    [(.commonBits32,false), (.commonBits128,true),
     (.fls128High, (node.bits ^^^ key) / 2^64 != 0)]
  else [(.commonBits32,false), (.commonBits128,false)]

theorem commonBits_run (node : AipNode) (key bits : Nat) (h : List Point) (w : World) :
    ((commonBits node key bits).run h).run w =
      .ok ((commonValue node key bits, h ++ choicePoints w (commonChoices node key bits)),
        records w (commonChoices node key bits)) := by
  cases width32 : (bits == 32) <;> cases width128 : (bits == 128) <;>
    cases high : ((node.bits ^^^ key) / 2^64 != 0) <;>
    simp [commonBits, commonValue, commonChoices, branchLogged, mark,
      branch, records, choicePoints, LookupMirror.record, width32, width128, high,
      List.append_assoc] <;> rfl

def swapChoices (bits : Nat) : Choices :=
  if bits == 32 then [(.swapEndian32,true)]
  else [(.swapEndian32,false), (.swapEndian128,bits == 128)]

theorem swapEndian_run (bits : Nat) (h : List Point) (w : World) :
    ((swapEndian bits).run h).run w =
      .ok (((),h ++ choicePoints w (swapChoices bits)), records w (swapChoices bits)) := by
  cases width32 : (bits == 32) <;>
    simp [swapEndian, swapChoices, branchLogged, mark, branch,
      records, choicePoints, LookupMirror.record, width32, List.append_assoc] <;> rfl

theorem choicePoints_world (w : World) (choices : Choices) (p : Point)
    (member : p ∈ choicePoints w choices) :
    p.world = {w with steps := p.world.steps} := by
  induction choices generalizing w with
  | nil => cases member
  | cons choice rest ih =>
    rcases choice with ⟨d,b⟩
    simp only [choicePoints, List.mem_cons] at member
    rcases member with rfl | member
    · rfl
    · exact ih (LookupMirror.record w d b) member

theorem records_world (w : World) (choices : Choices) :
    records w choices = {w with steps := (records w choices).steps} := by
  induction choices generalizing w with
  | nil => rfl
  | cons choice rest ih => exact ih (LookupMirror.record w choice.1 choice.2)

#print axioms commonBits_run
#print axioms lookup_accepted

/-- The three fields are the elaborated loop's early-return value, current
    node and latest peer-bearing node. A yielded iteration clears `answer`. -/

def iteration (bits key : Nat) (acc : Acc) : Logged (ForInStep Acc) := do
  let node := acc.2.1
  let mut found := acc.2.2
  match node with
  | none =>
    _ ← branchLogged .findNodeNode false
    return .done (some found, node, found)
  | some id =>
    _ ← branchLogged .findNodeNode true
    let n ← StateT.lift (getNode id)
    let matching ← prefixMatches n key bits
    if !(← branchLogged .findNodePrefixMatches matching) then
      return .done (some found, node, found)
    if ← branchLogged .findNodeHasPeer n.peer.isSome then found := some id
    if ← branchLogged .findNodeFullLength (n.cidr == bits) then
      return .done (some found, node, found)
    let bit ← StateT.lift (choose n key)
    let next ← StateT.lift (n.bitAt bit)
    return .yield (none, next, found)

def finish (acc : Acc) : Logged (Option NodeId) :=
  match acc.1 with
  | some result => pure result
  | none => StateT.lift (invariant "find_node deeper than MAX_ALLOWEDIPS_DEPTH")

theorem findNode_loop (trie : Option NodeId) (bits key : Nat) :
    findNode trie bits key = (do
      let acc ← forIn ([:130] : Std.Legacy.Range) (none,trie,none)
        (fun _ acc => iteration bits key acc)
      finish acc) := by
  unfold findNode iteration finish
  simp only [pure_bind]
  congr 1
  funext acc
  cases acc.1 <;> rfl

/-- Structural recursion on the mirror's actual remaining iteration budget.
    Done and yield retain precisely the logged history and World. -/
def loop (bits key : Nat) : Nat → Acc → Logged Acc
  | 0, acc => pure acc
  | fuel+1, acc => do
    match ← iteration bits key acc with
    | .done answer => pure answer
    | .yield next => loop bits key fuel next

theorem forIn_range'_loop (bits key start fuel : Nat) (acc : Acc) :
    forIn (List.range' start fuel) acc (fun _ acc => iteration bits key acc) =
      loop bits key fuel acc := by
  induction fuel generalizing start acc with
  | zero => rfl
  | succ fuel ih =>
    simp only [List.range'_succ, List.forIn_cons, loop]
    congr 1
    funext step
    cases step with
    | done answer => rfl
    | yield next => exact ih (start+1) next

theorem findNode_bounded (trie : Option NodeId) (bits key : Nat) :
    findNode trie bits key = (loop bits key 130 (none,trie,none) >>= finish) := by
  rw [findNode_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [forIn_range'_loop]
  rfl

/-- A successful bind has an actual intermediate state and accumulated log.
    This is useful when composing a machine region with one source phase. -/
theorem accepted_bind {a : Logged α} {f : α → Logged β}
    (history points : List Point) (world final : World) (answer : β)
    (accepted : ((a >>= f).run history).run world = .ok ((answer,points),final)) :
    ∃ value middle intermediate,
      (a.run history).run world = .ok ((value,middle),intermediate) ∧
      ((f value).run middle).run intermediate = .ok ((answer,points),final) := by
  cases first : (a.run history).run world with
  | error e =>
    simp only [StateT.run_bind, first] at accepted
    cases accepted
  | ok result =>
    obtain ⟨⟨value,middle⟩,intermediate⟩ := result
    refine ⟨value,middle,intermediate,rfl,?_⟩
    simp only [StateT.run_bind, first] at accepted
    exact accepted

theorem loop_succ_accepted (bits key fuel : Nat) (acc result : Acc)
    (history points : List Point) (world final : World)
    (accepted : ((loop bits key (fuel+1) acc).run history).run world =
      .ok ((result,points),final)) :
    ∃ step middle intermediate,
      ((iteration bits key acc).run history).run world = .ok ((step,middle),intermediate) ∧
      match step with
      | .done answer => result = answer ∧ points = middle ∧ final = intermediate
      | .yield next => ((loop bits key fuel next).run middle).run intermediate =
          .ok ((result,points),final) := by
  obtain ⟨step,middle,intermediate,first,rest⟩ :=
    accepted_bind history points world final result accepted
  refine ⟨step,middle,intermediate,first,?_⟩
  cases step with
  | done answer =>
    change Except.ok ((answer,middle),intermediate) = Except.ok ((result,points),final) at rest
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := Prod.mk.inj (Except.ok.inj rest)
    exact ⟨rfl,rfl,rfl⟩
  | yield next => exact rest

#print axioms findNode_bounded
#print axioms loop_succ_accepted

end Binary.AllowedipsSource
