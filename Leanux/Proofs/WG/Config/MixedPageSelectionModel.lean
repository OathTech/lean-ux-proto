import Leanux.Proofs.WG.Config.MixedPageScanModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Each remaining row is an actual occurrence. Only its first node list may
be a suffix, and its head is the real resumed cursor. -/
def MixedRowsSuffix (peers : PeerId → Peer) (rows : List MixedPeerRow) (ctx : DumpCtx) : Prop :=
  match rows with
  | [] => True
  | (pid,ids)::tail =>
    (match ctx.nextAllowedip with
    | none => (peers pid).allowedipsList = ids
    | some start => ids.head? = some start ∧ ∃ before, (peers pid).allowedipsList = before ++ ids) ∧
    ∀ row ∈ tail, (peers row.1).allowedipsList = row.2

/-- The cursor is precisely the peer occurrence immediately before the remaining
rows. This structural predicate does not yet assert first-match freshness. -/
def MixedPeerPosition (d : Device) (rows : List MixedPeerRow) (cursor : Option PeerId) : Prop :=
  match cursor with
  | none => d.peerList = rows.map Prod.fst
  | some old => ∃ before, d.peerList = before ++ old :: rows.map Prod.fst

/-- Freshness is required at computed boundaries only. Both tests cover the
entire consumed prefix, including prior pages and earlier positions in this page. -/
def MixedBoundaryFresh (d : Device) (peers : PeerId → Peer) (rows : List MixedPeerRow)
    (ctx : DumpCtx) (cursor : Option PeerId) : Prop :=
  (∀ old, cursor = some old → old ∉ d.peerList.take (d.peerList.length-rows.length-1)) ∧
  ∀ pid ids tail start, rows = (pid,ids)::tail → ctx.nextAllowedip = some start →
    start ∉ (peers pid).allowedipsList.take ((peers pid).allowedipsList.length-ids.length)

/-- Boundary constraints over the computed finite plan, not a supplied run. -/
def MixedPlanFresh (d : Device) (peers : PeerId → Peer) (pages : List MixedPeerScan) : Prop :=
  ∀ page ∈ pages.dropLast,
    MixedBoundaryFresh d peers page.remaining page.native.1 page.native.2.1

def mixedInitialRows (d : Device) (peers : PeerId → Peer) : List MixedPeerRow :=
  d.peerList.map (fun pid => (pid,(peers pid).allowedipsList))


end Leanux.Proofs.WG.Config
