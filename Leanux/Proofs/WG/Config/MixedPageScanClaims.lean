import Leanux.Proofs.WG.Config.MixedPageScanModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The weighted first-nonfit suffix never introduces occurrences. -/
theorem mixedPeerRemaining_length (nodes : NodeId → AipNode) (p : Peer) (ctx : DumpCtx)
    (skb : NlSkb) (ids : List NodeId) :
    (mixedPeerRemaining nodes p ctx skb ids).length ≤ ids.length := by
  have eq := congrArg List.length (weightedPrefix_spec nodes
    (skb.room-(if ctx.nextAllowedip.isNone then peerFixedSpace p else 40)-4) ids).1
  simp only [List.length_append] at eq
  dsimp only [mixedPeerRemaining]
  omega

/-- Exact serializer phase/rank behavior, including refusal of an unfit head. -/
theorem mixedPeerResult_progress (d : Device) (nodes : NodeId → AipNode) (p : Peer)
    (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId) :
    let result := weightedPeerResult d nodes p ctx skb ids
    match result.2.2 with
    | .complete _ => result.2.1.nextAllowedip = none
    | .split _ => result.2.1.nextAllowedip.isNone = false ∧
        (mixedPeerHeadFits nodes p ctx skb ids →
          (mixedPeerRemaining nodes p ctx skb ids).length < ids.length ∨ ctx.nextAllowedip.isNone = true)
    | .cancelled => result.2.1.nextAllowedip = ctx.nextAllowedip ∧
        ¬ mixedPeerHeadFits nodes p ctx skb ids := by
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  by_cases fitsPrefix : cost ≤ skb.room
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,
      ite_eq_left fitsPrefix]
    cases ids with
    | nil => simp [weightedAllowedResult]
    | cons first ids =>
      by_cases nest : skb.room-cost < 4
      · simp only [weightedAllowedResult,ite_eq_left nest]
        refine ⟨trivial,?_⟩
        simp only [mixedPeerHeadFits]
        change ¬ (cost+4 ≤ skb.room ∧ _)
        omega
      · simp only [weightedAllowedResult,ite_eq_right nest]
        cases plan : weightedPrefix nodes (skb.room-cost-4) (first::ids) with
        | mk front remaining =>
          cases remaining with
          | nil => simp
          | cons next rest =>
            refine ⟨rfl,?_⟩
            intro fit
            rcases fit.2 with fresh | one
            · exact .inr fresh
            · left
              change dumpNodeSpace (nodes first) ≤ skb.room-cost-4 at one
              have full := weightedPrefix_spec nodes (skb.room-cost-4) (first::ids)
              rw [plan] at full
              have starts : front ≠ [] := by
                simp only [weightedPrefix,ite_eq_left one] at plan
                exact fun empty => by simp [empty] at plan
              have lengths := congrArg List.length full.1
              simp only [List.length_append,List.length_cons] at lengths
              have positive : 0 < front.length := by cases front <;> simp_all
              simp only [mixedPeerRemaining,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,plan]
              simp only [List.length_cons]
              omega
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,
      ite_eq_right fitsPrefix]
    refine ⟨trivial,?_⟩
    cases ids with
    | nil => exact fitsPrefix
    | cons first ids =>
      simp only [mixedPeerHeadFits]
      change ¬ (cost+4 ≤ skb.room ∧ _)
      omega

/-- The finite peer scan never increases unconsumed occurrence/phase work,
including cancellation at any position. -/
theorem mixedPeerScan_nonincrease (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (skb : NlSkb) (prior : Array PeerDumpAttrs) :
    let result := mixedPeerScan d peers nodes rows ctx cursor skb prior
    mixedPageMeasure result.remaining result.native.1 ≤ mixedPageMeasure rows ctx := by
  induction rows generalizing ctx cursor skb prior with
  | nil => exact Nat.le_refl _
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    have one := mixedPeerResult_progress d nodes (peers pid) ctx skb ids
    cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk out rest =>
      obtain ⟨after,verdict⟩ := rest
      rw [outcome] at one
      cases verdict with
      | complete attrs =>
        dsimp only at one
        have tail := ih after (some pid) out (prior.push attrs)
        simp only [mixedPeerScan,outcome]
        apply Nat.le_trans tail
        simp only [mixedPageMeasure,mixedRowsWeight,one,Option.isNone_none,ite_true]
        split <;> omega
      | split attrs =>
        dsimp only at one
        have length := mixedPeerRemaining_length nodes (peers pid) ctx skb ids
        simp only [mixedPeerScan,outcome,mixedPageMeasure,mixedRowsWeight,one.1,Bool.false_eq_true,ite_false]
        split <;> omega
      | cancelled =>
        dsimp only at one
        simp only [mixedPeerScan,outcome,mixedPageMeasure,one.1]
        exact Nat.le_refl _

/-- A nonempty callback advances when its actual first serializer can progress.
Later cancellation is allowed: an earlier complete peer already decreased work. -/
theorem mixedPeerScan_progress (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (pid : PeerId) (ids : List NodeId) (rows : List MixedPeerRow)
    (ctx : DumpCtx) (cursor : Option PeerId) (skb : NlSkb) (prior : Array PeerDumpAttrs)
    (fits : mixedPeerHeadFits nodes (peers pid) ctx skb ids) :
    let result := mixedPeerScan d peers nodes ((pid,ids)::rows) ctx cursor skb prior
    mixedPageMeasure result.remaining result.native.1 < mixedPageMeasure ((pid,ids)::rows) ctx := by
  have one := mixedPeerResult_progress d nodes (peers pid) ctx skb ids
  cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
  | mk out rest =>
    obtain ⟨after,verdict⟩ := rest
    rw [outcome] at one
    cases verdict with
    | complete attrs =>
      dsimp only at one
      have tail := mixedPeerScan_nonincrease d peers nodes rows after (some pid) out (prior.push attrs)
      simp only [mixedPeerScan,outcome]
      apply Nat.lt_of_le_of_lt tail
      simp only [mixedPageMeasure,mixedRowsWeight,one,Option.isNone_none,ite_true]
      split <;> omega
    | split attrs =>
      dsimp only at one
      have length := mixedPeerRemaining_length nodes (peers pid) ctx skb ids
      have progress := one.2 fits
      simp only [mixedPeerScan,outcome,mixedPageMeasure,mixedRowsWeight,one.1,Bool.false_eq_true,ite_false]
      rcases progress with less | fresh
      · split <;> omega
      · simp only [fresh,ite_true]
        omega
    | cancelled => exact False.elim (one.2 fits)

end Leanux.Proofs.WG.Config
