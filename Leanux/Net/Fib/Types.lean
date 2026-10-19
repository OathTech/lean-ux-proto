import Std.Data.TreeMap
import Lean.Data.Json

/-!
# The IPv4 FIB trie: state (net/ipv4/fib_trie.c, fib_semantics.c)

Lane C (docs/2026-10-15-design-c-fib-trie.md, section 3.1). The trie is the
C's shape: a `key_vector` is a leaf with its alias list or a tnode with its
child array and the counts `empty_children`/`full_children` (fib_trie.c:120-137).
The root is the C's `t->kv`, a tnode with `pos = KEYLENGTH` holding one
child (:2411). The parent pointer is not represented: every walk keeps its
path explicitly (what `resize`, `node_pull_suffix` and the lookup's
backtrace read from it); `update_children`'s test on parent identity (:462)
is reproduced by the `fresh` mark on the nodes a resize step creates.

On this configuration (`CONFIG_IP_MULTIPLE_TABLES` unset) the local table is
an alias of the main table (fib_frontend.c:50-71, fib_trie.c:2390-2420): one
trie, the aliases told apart by `tbId`. `fib_info`s are shared by identity
(`fib_find_info`, fib_semantics.c:409-437) and live in a map with their
tree reference counts.
-/

namespace Leanux.Net.Fib

/-- The `__be32` word of a host-order IPv4 address: the C compares addresses
    in network byte order (`fib_prefsrc`, `fc_prefsrc`), so a recorded
    operand is this word. -/
def be32 (x : Nat) : Nat :=
  x % 256 * 2 ^ 24 + x / 2 ^ 8 % 256 * 2 ^ 16 + x / 2 ^ 16 % 256 * 2 ^ 8 + x / 2 ^ 24 % 256

open Std

abbrev KEYLENGTH : Nat := 32
abbrev KEY_MAX : Nat := 2 ^ 32 - 1

/-- `fib_props` (fib_semantics.c:99-147): the route types the fixture and the
    corpus use, with their error (`.error`) and minimum scope (`.scope`). -/
inductive RouteType where
  | unspec | unicast | local | broadcast | anycast | multicast
  | blackhole | unreachable | prohibit | throw
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `rtm_type` numbers (include/uapi/linux/rtnetlink.h). -/
def RouteType.code : RouteType → Nat
  | .unspec => 0 | .unicast => 1 | .local => 2 | .broadcast => 3 | .anycast => 4
  | .multicast => 5 | .blackhole => 6 | .unreachable => 7 | .prohibit => 8 | .throw => 9

def RouteType.ofCode? : Nat → Option RouteType
  | 0 => some .unspec | 1 => some .unicast | 2 => some .local | 3 => some .broadcast | 4 => some .anycast
  | 5 => some .multicast | 6 => some .blackhole | 7 => some .unreachable | 8 => some .prohibit | 9 => some .throw
  | _ => none

/-- `fib_props[type].error` (fib_semantics.c:99-147): 0, or the negative errno
    of a rejecting type. -/
def RouteType.error : RouteType → Int
  | .blackhole => -22      -- -EINVAL
  | .unreachable => -113   -- -EHOSTUNREACH
  | .prohibit => -13       -- -EACCES
  | .throw => -11          -- -EAGAIN
  | _ => 0

/-- `RT_SCOPE_*`: universe 0, link 253, host 254, nowhere 255. -/
abbrev RT_SCOPE_UNIVERSE : Nat := 0
abbrev RT_SCOPE_LINK : Nat := 253
abbrev RT_SCOPE_HOST : Nat := 254
abbrev RT_SCOPE_NOWHERE : Nat := 255

/-- `fib_props[type].scope`, the type's minimum scope (fib_semantics.c:99-147). -/
def RouteType.minScope : RouteType → Nat
  | .unspec => RT_SCOPE_NOWHERE
  | .local => RT_SCOPE_HOST
  | .broadcast | .anycast => RT_SCOPE_LINK
  | _ => RT_SCOPE_UNIVERSE

/-- `RT_TABLE_MAIN` 254, `RT_TABLE_LOCAL` 255. -/
abbrev RT_TABLE_MAIN : Nat := 254
abbrev RT_TABLE_LOCAL : Nat := 255

/-- `RTPROT_*`: kernel 2, static 4. -/
abbrev RTPROT_KERNEL : Nat := 2
abbrev RTPROT_STATIC : Nat := 4

/-- `RTNH_F_DEAD` 1, `RTNH_F_LINKDOWN` 16 (rtnetlink.h). -/
abbrev RTNH_F_DEAD : Nat := 1
abbrev RTNH_F_LINKDOWN : Nat := 16
/-- `RTNH_COMPARE_MASK`: dead, linkdown, offload and trap (rtnetlink.h:426-427). -/
abbrev RTNH_COMPARE_MASK : Nat := 1 ||| 16 ||| 8 ||| 64

abbrev FibInfoId := Nat

/-- One `struct fib_info` with its single nexthop (`CONFIG_IP_ROUTE_MULTIPATH`
    unset; `struct fib_nh` embedded, fib_semantics.c:1415-1660). `treeref`
    is `fib_treeref` (the aliases holding it); `dead` is `fib_dead`. The
    nexthop's cached source and its generation are `nh_saddr` and
    `nh_saddr_genid` (:1354-1369). -/
structure FibInfo where
  protocol : Nat
  scope : Nat
  flags : Nat := 0
  priority : Nat := 0
  prefsrc : Nat := 0
  type : RouteType
  tbId : Nat
  /-- `RTAX_MTU` of the route's metrics, when the route carries one (the W4
      routes mode); 0 is the metric's absence (`dst_default_metrics`). -/
  mtu : Nat := 0
  dead : Bool := false
  treeref : Nat := 1
  -- the nexthop
  oif : Nat
  /-- The nexthop's device (ifindex), `fib_nh_dev`; 0 for a route type with
      an error (no nexthop device). -/
  dev : Nat := 0
  nhScope : Nat := RT_SCOPE_NOWHERE
  nhFlags : Nat := 0
  nhSaddr : Nat := 0
  nhSaddrGenid : Nat := 0
  deriving Repr, BEq, Inhabited

/-- The identity `fib_find_info` compares (fib_semantics.c:409-437): protocol,
    scope, prefsrc, priority, type, table, metrics, the flags outside
    `RTNH_COMPARE_MASK`, and the nexthop (`nh_comp`: oif, gateway, flags
    outside the mask). -/
def FibInfo.sameIdentity (a b : FibInfo) : Bool :=
  a.protocol == b.protocol && a.scope == b.scope && a.prefsrc == b.prefsrc && a.priority == b.priority
  && a.type == b.type && a.tbId == b.tbId && a.mtu == b.mtu
  && ((a.flags ^^^ b.flags) &&& (0xffffffff - RTNH_COMPARE_MASK)) == 0
  && a.oif == b.oif && a.nhScope == b.nhScope

/-- One `struct fib_alias` (fib_trie.c, ip_fib.h): the suffix length
    `KEYLENGTH - plen`, the table, the DSCP, the type, the accessed bit
    (`FA_S_ACCESSED`), the info and `fa_default`. -/
structure FibAlias where
  slen : Nat
  tbId : Nat
  dscp : Nat := 0
  type : RouteType
  accessed : Bool := false
  info : FibInfoId
  faDefault : Int := -1
  deriving Repr, BEq, Inhabited

/-- `struct key_vector` with its `tnode` counts (fib_trie.c:120-137). A leaf
    has `bits = 0` and its aliases; a tnode has `bits > 0`, `2^bits` child
    slots, `emptyChildren` and `fullChildren` (`t_key`-wide counters), and
    the `fresh` mark of 3.1. `key` is the C's `t_key` in host order; `slen`
    the suffix length (:710-743). -/
inductive KeyVector where
  | leaf (key : Nat) (slen : Nat) (aliases : List FibAlias)
  | tnode (key pos bits slen : Nat) (children : Array (Option KeyVector))
      (emptyChildren fullChildren : Nat) (fresh : Bool)

namespace KeyVector

def key : KeyVector → Nat
  | .leaf k _ _ => k
  | .tnode k _ _ _ _ _ _ _ => k

def pos : KeyVector → Nat
  | .leaf _ _ _ => 0
  | .tnode _ p _ _ _ _ _ _ => p

def bits : KeyVector → Nat
  | .leaf _ _ _ => 0
  | .tnode _ _ b _ _ _ _ _ => b

def slen : KeyVector → Nat
  | .leaf _ s _ => s
  | .tnode _ _ _ s _ _ _ _ => s

def isLeaf : KeyVector → Bool
  | .leaf .. => true
  | .tnode .. => false

/-- `IS_TRIE(n)`: `pos >= KEYLENGTH` (:117). -/
def isTrie (n : KeyVector) : Bool := n.pos ≥ KEYLENGTH

def children : KeyVector → Array (Option KeyVector)
  | .leaf .. => #[]
  | .tnode _ _ _ _ c _ _ _ => c

def emptyChildren : KeyVector → Nat
  | .leaf .. => 0
  | .tnode _ _ _ _ _ e _ _ => e

def fullChildren : KeyVector → Nat
  | .leaf .. => 0
  | .tnode _ _ _ _ _ _ f _ => f

def fresh : KeyVector → Bool
  | .leaf .. => false
  | .tnode _ _ _ _ _ _ _ f => f

def aliases : KeyVector → List FibAlias
  | .leaf _ _ a => a
  | .tnode .. => []

def withSlen (n : KeyVector) (s : Nat) : KeyVector :=
  match n with
  | .leaf k _ a => .leaf k s a
  | .tnode k p b _ c e f fr => .tnode k p b s c e f fr

def withAliases (n : KeyVector) (a : List FibAlias) : KeyVector :=
  match n with
  | .leaf k s _ => .leaf k s a
  | t => t

def withChildren (n : KeyVector) (c : Array (Option KeyVector)) : KeyVector :=
  match n with
  | .tnode k p b s _ e f fr => .tnode k p b s c e f fr
  | l => l

def withCounts (n : KeyVector) (e f : Nat) : KeyVector :=
  match n with
  | .tnode k p b s c _ _ fr => .tnode k p b s c e f fr
  | l => l

def withFresh (n : KeyVector) (fr : Bool) : KeyVector :=
  match n with
  | .tnode k p b s c e f _ => .tnode k p b s c e f fr
  | l => l

def child (n : KeyVector) (i : Nat) : Option KeyVector :=
  match n with
  | .tnode _ _ _ _ c _ _ _ => (c.getD i none)
  | .leaf .. => none

/-- `child_length(tn)`: `(1ul << tn->bits) & ~1ul` (:214-217), 0 for a leaf. -/
def childLength (n : KeyVector) : Nat := if n.bits == 0 then 0 else 2 ^ n.bits

/-- `get_cindex(key, kv)`: `(key ^ kv->key) >> kv->pos` (:219). -/
def getCindex (key : Nat) (kv : KeyVector) : Nat := (key ^^^ kv.key) >>> kv.pos

/-- `get_index(key, kv)` (:221-229): 0 at the root (`KEYLENGTH == kv->pos`),
    else `get_cindex`. -/
def getIndex (key : Nat) (kv : KeyVector) : Nat :=
  if kv.pos == KEYLENGTH then 0 else (key ^^^ kv.key) >>> kv.pos

/-- `prefix_mismatch(key, n)`: `(key ^ prefix) & (prefix | -prefix)` on
    `t_key` (:1401-1406). -/
def prefixMismatch (key : Nat) (n : KeyVector) : Nat :=
  let p := n.key
  let neg := (2 ^ 32 - p) % 2 ^ 32   -- `-prefix` on u32
  ((key ^^^ p) &&& (p ||| neg)) &&& KEY_MAX

/-- Structural equality, bounded by the trie's depth. -/
def beqFuel : Nat → KeyVector → KeyVector → Bool
  | _, .leaf k s a, .leaf k' s' a' => k == k' && s == s' && a == a'
  | fuel + 1, .tnode k p b s c e f fr, .tnode k' p' b' s' c' e' f' fr' =>
    k == k' && p == p' && b == b' && s == s' && e == e' && f == f' && fr == fr' && c.size == c'.size
    && (List.range c.size).all fun i => match c[i]!, c'[i]! with
      | none, none => true
      | some x, some y => beqFuel fuel x y
      | _, _ => false
  | _, _, _ => false

instance : BEq KeyVector := ⟨beqFuel (KEYLENGTH + 2)⟩

def reprFuel : Nat → KeyVector → String
  | _, .leaf k s a => s!"leaf {k} slen={s} aliases={repr a}"
  | 0, .tnode k p b .. => s!"tnode {k} pos={p} bits={b} ..."
  | fuel + 1, .tnode k p b s c e f fr =>
    s!"tnode {k} pos={p} bits={b} slen={s} empty={e} full={f} fresh={fr} [" ++
      ", ".intercalate (c.toList.map fun x => match x with | none => "-" | some y => reprFuel fuel y) ++ "]"

instance : Repr KeyVector := ⟨fun n _ => reprFuel (KEYLENGTH + 2) n⟩

end KeyVector

/-- The root's child (`t->kv->tnode[0]`): the trie as the C holds it, with
    the root's `pos = KEYLENGTH` and `slen = KEYLENGTH` (:2411-2412). -/
structure Trie where
  /-- `t->kv[0].tnode[0]`: the root's one child, or an empty trie. -/
  root : Option KeyVector := none
  /-- The root's own `slen` (:2412), raised by `node_push_suffix` as the
      C's root participates in the suffix walks. -/
  rootSlen : Nat := KEYLENGTH
  deriving Inhabited, BEq, Repr

/-- `struct fib_table` (one for the two aliased tables, 1.1 of the design):
    `tb_num_default` per table id (the C keeps one per `fib_table`, and the
    LOCAL alias shares `tb_data` but has its own `tb_num_default`, :2404). -/
structure Table where
  trie : Trie := {}
  numDefaultMain : Nat := 0
  numDefaultLocal : Nat := 0
  /-- `fib_info`s by identity, with their tree references. -/
  infos : TreeMap FibInfoId FibInfo := {}
  nextInfo : FibInfoId := 0
  /-- `net->ipv4.fib_has_custom_local_routes` (fib_frontend.c:918-919). -/
  customLocalRoutes : Bool := false
  /-- `net->ipv4.rt_genid` (`rt_cache_flush`, route.c:406-409), the
      generation the dst caches compare. -/
  rtGenid4 : Nat := 0
  /-- `net->ipv4.dev_addr_genid` (fib_frontend.c:1458/1463/1505; a random
      start the mirror counts from 0, its comparison's operands excluded). -/
  devAddrGenid : Nat := 0
  deriving Inhabited, BEq, Repr

/-- The root `key_vector` as a `KeyVector` for the walks that treat the root
    as a node (`fib_find_node`'s `pn`, the backtrace's `IS_TRIE(pn)`): a
    tnode with `pos = KEYLENGTH`, `bits = 0` is the C's shape (:2411), whose
    one child is `trie.root`. -/
def Trie.rootVector (t : Trie) : KeyVector :=
  .tnode 0 KEYLENGTH 0 t.rootSlen #[t.root] 0 0 false

end Leanux.Net.Fib
