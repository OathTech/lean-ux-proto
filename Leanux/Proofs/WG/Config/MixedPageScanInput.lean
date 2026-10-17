import Leanux.Proofs.WG.Config.MixedPageScanModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The first row is the actual fresh list or selected resumed suffix;
every later row still names its peer's full allowed-IP list. -/
def MixedRowsSelected (peers : PeerId → Peer) (rows : List MixedPeerRow) (ctx : DumpCtx) : Prop :=
  match rows with
  | [] => True
  | (pid,ids) :: rest =>
    (match ctx.nextAllowedip with
    | none => (peers pid).allowedipsList = ids
    | some start => ids.head? = some start ∧ (peers pid).allowedipsList.dropWhile (· != start) = ids) ∧
    ∀ row ∈ rest, (peers row.1).allowedipsList = row.2

/-- Completing a peer resets its allowed-IP cursor and sequence before the
next peer is visited; the held peer cursor is unchanged. -/
theorem weightedPeerResult_complete_context (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId) (attrs : PeerDumpAttrs)
    (complete : (weightedPeerResult d nodes p ctx skb ids).2.2 = .complete attrs) :
    (weightedPeerResult d nodes p ctx skb ids).2.1 =
      {ctx with nextAllowedip := none,allowedipsSeq := 0} := by
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  change (if cost ≤ skb.room then
    weightedAllowedResult d nodes ctx skb {skb with room := skb.room-cost}
      (hexKey p.remoteStatic)
      (if ctx.nextAllowedip.isNone then peerFixedAttrs p else [("public_key",toJson (hexKey p.remoteStatic))])
      ids else (skb,ctx,.cancelled)).2.2 = .complete attrs at complete
  change (if cost ≤ skb.room then
    weightedAllowedResult d nodes ctx skb {skb with room := skb.room-cost}
      (hexKey p.remoteStatic)
      (if ctx.nextAllowedip.isNone then peerFixedAttrs p else [("public_key",toJson (hexKey p.remoteStatic))])
      ids else (skb,ctx,.cancelled)).2.1 = _
  by_cases enough : cost ≤ skb.room
  · simp only [ite_eq_left enough] at complete ⊢
    cases ids with
    | nil => rfl
    | cons id ids =>
      simp only [weightedAllowedResult] at complete ⊢
      by_cases short : skb.room-cost < 4
      · simp only [ite_eq_left short] at complete
        cases complete
      · simp only [ite_eq_right short] at complete ⊢
        cases remaining : (weightedPrefix nodes (skb.room-cost-4) (id::ids)).2 with
        | nil => rfl
        | cons next rest =>
          simp only [remaining] at complete
          cases complete
  · simp only [ite_eq_right enough] at complete
    cases complete

end Leanux.Proofs.WG.Config
