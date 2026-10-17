import Leanux.Proofs.WG.Config.MixedPagePlanModel
import Leanux.Proofs.WG.Config.CursorCallbackModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Pure DATA content of a planned scan. The preserved nextPeer is the input
cursor, so split-current-peer pages with no completed cursor repeat the header.
The empty Device guard emits no peer nest; this model alone is not a callback. -/
def mixedPageMessage (d : Device) (page : MixedPeerScan) : NlMessage :=
  .data 2 (if page.native.1.nextPeer.isNone then deviceFixedAttrs d else [])
    (if d.peerList.isEmpty then none else some page.native.2.2.2.2.toList)

/-- Exact callback data after cursor finalization, with fixed successful flags.
Whole native correspondence separately discharges guards and reference handling. -/
def mixedPageCall (d : Device) (page : MixedPeerScan) : DumpCall :=
  cursorCallResult d 2 (if page.native.1.nextPeer.isNone then deviceFixedAttrs d else [])
    page.native.1 page.native.2.1 page.native.2.2.1 page.native.2.2.2.1
    (if d.peerList.isEmpty then none else some page.native.2.2.2.2)

/-- Planned raw DATA order followed by the successful DONE. Native source
correspondence supplies unchanged generation and the guard/lifetime conditions. -/
def mixedPageMessages (d : Device) (pages : List MixedPeerScan) : List NlMessage :=
  pages.map (mixedPageMessage d) ++ [.done 2 0]

/-- Static receive budget: every DATA page, and one further receive exactly
when the last DATA has insufficient room for DONE. The empty-list case is only
a total definition; the canonical plan below is nonempty. -/
def mixedPageReceiveCount (pages : List MixedPeerScan) : Nat :=
  match pages.getLast? with
  | none => 0
  | some last => pages.length + if last.native.2.2.1.room < nlmsgTotal 4 then 1 else 0

end Leanux.Proofs.WG.Config
