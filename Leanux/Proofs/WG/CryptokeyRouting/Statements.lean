import Leanux.Proofs.WG.AllowedIps.ArithmeticMirror

/-!
# R3: the prefix-arithmetic component of cryptokey routing

These statements connect the original arithmetic helpers to leading-bit
prefixes. Trie mutation, longest-prefix lookup over a configuration history,
and packet admission are the remaining components of the routing result.
-/

namespace Leanux.Proofs.WG.CryptokeyRouting

open Leanux
open Leanux.Proofs.WG.AllowedIps

/-- For bounded IPv4 or IPv6 addresses, the original `commonBits` returns
their maximal common-prefix length: every bounded CIDR is at most that
length exactly when the corresponding leading address bits agree. The
execution equation includes all of the mirror's branch records. -/
theorem commonBits_correct (n : WG.AipNode) (key width : Nat) (w : World)
    (hw : width = 32 ∨ width = 128) (hn : n.bits < 2 ^ width)
    (hk : key < 2 ^ width) :
    (WG.commonBits n key width).run w =
        .ok (common width n.bits key, commonRecords w width (n.bits ^^^ key)) ∧
      common width n.bits key ≤ width ∧
      ∀ cidr, cidr ≤ width →
        (cidr ≤ common width n.bits key ↔
          prefixBits width cidr n.bits = prefixBits width cidr key) := by
  exact ⟨commonBits_run n key width w hw, common_le _ _ _,
    fun _ hc => common_ge_iff hn hk hc⟩

/-- For bounded IPv4 or IPv6 addresses and a CIDR within the family width,
the original `prefixMatches` returns true exactly when the node and query
have equal leading prefix bits, with exactly its recorded World effects. -/
theorem prefixMatches_correct (n : WG.AipNode) (key width : Nat) (w : World)
    (hw : width = 32 ∨ width = 128) (hn : n.bits < 2 ^ width)
    (hk : key < 2 ^ width) (hc : n.cidr ≤ width) :
    (WG.prefixMatches n key width).run w =
      .ok (decide (prefixBits width n.cidr n.bits = prefixBits width n.cidr key),
        commonRecords w width (n.bits ^^^ key)) :=
  prefixMatches_run n key width w hw hn hk hc

/-- Whenever the node has another address bit to inspect, the original
`choose` returns that next bit, either zero or one, and preserves the World.
This arithmetic statement is uniform in the node's address width. -/
theorem choose_correct (n : WG.AipNode) (key : Nat) (w : World) (hc : n.cidr < n.bitlen) :
    (WG.choose n key).run w =
        .ok (prefixBits n.bitlen (n.cidr + 1) key % 2, w) ∧
      prefixBits n.bitlen (n.cidr + 1) key % 2 < 2 := by
  constructor
  · simpa only [bit_eq_prefix_succ] using choose_run n key w hc
  · exact Nat.mod_lt _ (by decide)

end Leanux.Proofs.WG.CryptokeyRouting
