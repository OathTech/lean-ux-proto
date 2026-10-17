import Leanux.Proofs.WG.Config.MixedPageBoundaryModel
import Leanux.Proofs.WG.Config.MixedPageScanClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- A retained nonempty scan boundary has either completed a peer or entered
resumed AIP phase. No selected-cursor premise is assumed. -/
theorem mixedPeerScan_boundary (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (skb : NlSkb) (prior : Array PeerDumpAttrs) :
    let result := mixedPeerScan d peers nodes rows ctx cursor skb prior
    (cursor.isSome = true → result.native.2.1.isSome = true) ∧
    (∀ pid ids tail, rows = (pid,ids)::tail → mixedPeerHeadFits nodes (peers pid) ctx skb ids →
      result.native.1.nextAllowedip.isNone = true → result.native.2.1.isSome = true) := by
  induction rows generalizing ctx cursor skb prior with
  | nil => simp [mixedPeerScan]
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    have one := mixedPeerResult_progress d nodes (peers pid) ctx skb ids
    cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk out rest =>
      obtain ⟨after,verdict⟩ := rest
      rw [outcome] at one
      cases verdict with
      | complete attrs =>
        have tail := (ih after (some pid) out (prior.push attrs)).1 rfl
        simp only [mixedPeerScan,outcome]
        exact ⟨fun _ => tail,fun _ _ _ _ _ _ => tail⟩
      | split attrs =>
        dsimp only at one
        simp only [mixedPeerScan,outcome]
        refine ⟨fun h => h,?_⟩
        intro q ns tail same fits fresh
        exact False.elim (by rw [one.1] at fresh; contradiction)
      | cancelled =>
        dsimp only at one
        simp only [mixedPeerScan,outcome]
        refine ⟨fun h => h,?_⟩
        intro q ns tail same fits fresh
        cases same
        exact False.elim (one.2 fits)

/-- A split retains a real nonempty suffix, not an artificial continuation. -/
theorem mixedPeerResult_split_remaining (d : Device) (nodes : NodeId → AipNode) (p : Peer)
    (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId) (out : NlSkb) (after : DumpCtx)
    (attrs : PeerDumpAttrs)
    (splitResult : weightedPeerResult d nodes p ctx skb ids = (out,after,.split attrs)) :
    mixedPeerRemaining nodes p ctx skb ids ≠ [] := by
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  by_cases fitsPrefix : cost ≤ skb.room
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,
      ite_eq_left fitsPrefix] at splitResult
    cases ids with
    | nil => simp [weightedAllowedResult] at splitResult
    | cons first ids =>
      by_cases nest : skb.room-cost < 4
      · simp [weightedAllowedResult,nest] at splitResult
      · simp only [weightedAllowedResult,ite_eq_right nest] at splitResult
        cases plan : weightedPrefix nodes (skb.room-cost-4) (first::ids) with
        | mk front remaining =>
          rw [plan] at splitResult
          cases remaining with
          | nil => simp at splitResult
          | cons next rest =>
            simp only [mixedPeerRemaining,
              show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,plan]
            simp
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,
      ite_eq_right fitsPrefix] at splitResult
    simp at splitResult

theorem mixedPeerScan_done (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (skb : NlSkb) (prior : Array PeerDumpAttrs) :
    let result := mixedPeerScan d peers nodes rows ctx cursor skb prior
    result.native.2.2.2.1 = true ↔ result.remaining = [] := by
  induction rows generalizing ctx cursor skb prior with
  | nil => simp [mixedPeerScan]
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk out rest =>
      obtain ⟨after,verdict⟩ := rest
      cases verdict <;> simp only [mixedPeerScan,outcome]
      · exact ih _ _ _ _
      · simp
      · simp

/-- The real resumed header leaves enough room for any fixed prefix and nest. -/
theorem mixedPeerHeadFits_large (nodes : NodeId → AipNode) (p : Peer) (ctx : DumpCtx)
    (skb : NlSkb) (ids : List NodeId) (large : 172 ≤ skb.room) :
    mixedPeerHeadFits nodes p ctx skb ids := by
  have bound := peerFixedSpace_bound p
  cases ids with
  | nil => simp only [mixedPeerHeadFits]; split <;> omega
  | cons first ids =>
    have node := dumpNodeSpace_bounds (nodes first)
    simp only [mixedPeerHeadFits]
    split
    · exact ⟨by omega,Or.inl (by assumption)⟩
    · exact ⟨by omega,Or.inr (by omega)⟩

theorem mixedPeerHeadFits_resumed (nodes : NodeId → AipNode) (p : Peer) (ctx : DumpCtx)
    (skb : NlSkb) (ids : List NodeId) (resumed : ctx.nextAllowedip.isNone = false)
    (large : 84 ≤ skb.room) : mixedPeerHeadFits nodes p ctx skb ids := by
  cases ids with
  | nil => simp only [mixedPeerHeadFits,resumed,Bool.false_eq_true,ite_false]; omega
  | cons first ids =>
    have node := dumpNodeSpace_bounds (nodes first)
    simp only [mixedPeerHeadFits,resumed,Bool.false_eq_true,ite_false,false_or]
    omega

/-- Static readiness propagates to the next planned header. With no completed
cursor a nonfinal boundary is resumed; otherwise the normal header has ample room. -/
theorem mixedPageReady_next (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx) :
    let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
    result.remaining ≠ [] → MixedPageReady d peers nodes result.remaining
      {result.native.1 with nextPeer := result.native.2.1} := by
  intro result nonempty
  rcases ready with empty | ⟨room,head⟩
  · subst rows
    exact False.elim (nonempty rfl)
  cases rows with
  | nil => exact False.elim (nonempty rfl)
  | cons row rows =>
    obtain ⟨pid,ids⟩ := row
    have fits := head pid ids rows rfl
    have boundary := mixedPeerScan_boundary d peers nodes ((pid,ids)::rows) ctx ctx.nextPeer
      {room := mixedPageRoom d ctx} #[]
    change (ctx.nextPeer.isSome = true → result.native.2.1.isSome = true) ∧ _ at boundary
    cases cursor : result.native.2.1 with
    | some next =>
      right
      refine ⟨by change 84 ≤ NLMSG_GOODSIZE-24; decide,?_⟩
      intro q ns tail same
      apply mixedPeerHeadFits_large
      change 172 ≤ NLMSG_GOODSIZE-24
      decide
    | none =>
      have initial : ctx.nextPeer = none := by
        cases old : ctx.nextPeer with
        | none => rfl
        | some value =>
          have impossible := boundary.1 (by simp [old])
          simp [cursor] at impossible
      have phase : result.native.1.nextAllowedip.isNone = false := by
        cases value : result.native.1.nextAllowedip.isNone
        · rfl
        · have impossible := boundary.2 pid ids rows rfl fits value
          change result.native.2.1.isSome = true at impossible
          simp [cursor] at impossible
      have space : 84 ≤ NLMSG_GOODSIZE-devicePrefixSpace d := by
        simpa only [mixedPageRoom,initial,Option.isNone_none,ite_true] using room
      right
      refine ⟨space,?_⟩
      intro q ns tail same
      exact mixedPeerHeadFits_resumed nodes (peers q) _ _ ns phase space

/-- Any unfinished statically ready scan strictly reduces the occurrence measure. -/
theorem mixedPageReady_progress (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx) :
    let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
    result.remaining ≠ [] →
      mixedPageMeasure result.remaining {result.native.1 with nextPeer := result.native.2.1} <
        mixedPageMeasure rows ctx := by
  intro result unfinished
  have nonempty : rows ≠ [] := by
    intro empty
    subst rows
    exact unfinished rfl
  obtain ⟨pid,ids,tail,rowsEq⟩ : ∃ pid ids tail, rows = (pid,ids)::tail := by
    cases rows with
    | nil => contradiction
    | cons row tail => exact ⟨row.1,row.2,tail,rfl⟩
  have fits := (ready.resolve_left nonempty).2 pid ids tail rowsEq
  have progress := mixedPeerScan_progress d peers nodes pid ids tail ctx ctx.nextPeer
    {room := mixedPageRoom d ctx} #[] fits
  subst rows
  simpa only [mixedPageMeasure] using progress

/-- Fresh first-head fit already supplies the minimal continuation room.
The empty input has a single completed pure scan without a room premise.
Native header and guard obligations are separate. -/
theorem mixedPageReady_fresh (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (fresh : ctx.nextAllowedip = none)
    (head : ∀ pid ids tail, rows = (pid,ids)::tail →
      mixedPeerHeadFits nodes (peers pid) ctx {room := mixedPageRoom d ctx} ids) :
    MixedPageReady d peers nodes rows ctx := by
  cases rows with
  | nil => exact Or.inl rfl
  | cons row rows =>
    obtain ⟨pid,ids⟩ := row
    have fits := head pid ids rows rfl
    have cost : 136 ≤ peerFixedSpace (peers pid) := by
      unfold peerFixedSpace
      omega
    right
    refine ⟨?_,head⟩
    cases ids with
    | nil => simp only [mixedPeerHeadFits,fresh,Option.isNone_none,ite_true] at fits; omega
    | cons first ids =>
      simp only [mixedPeerHeadFits,fresh,Option.isNone_none,ite_true] at fits
      omega


end Leanux.Proofs.WG.Config
