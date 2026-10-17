import Leanux.Proofs.WG.Config.MixedPagePlanModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The canonical plan ends at a completed planned scan. Every preceding scan
is nonfinal, and the occurrence measure gives a finite page bound. -/
theorem mixedPages_complete (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx) :
    ∃ front last, mixedPages d peers nodes rows ctx ready = front ++ [last] ∧
      last.remaining = [] ∧ last.native.2.2.2.1 = true ∧
      (∀ page ∈ front, page.native.2.2.2.1 = false) ∧
      (mixedPages d peers nodes rows ctx ready).length ≤ mixedPageMeasure rows ctx + 1 := by
  let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  have done := mixedPeerScan_done d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  change result.native.2.2.2.1 = true ↔ result.remaining = [] at done
  rw [mixedPages]
  dsimp only
  by_cases finished : result.remaining = []
  · rw [dite_eq_left finished]
    refine ⟨[],result,rfl,finished,done.mpr finished,by simp,?_⟩
    simp
  · rw [dite_eq_right finished]
    have nextReady := mixedPageReady_next d peers nodes rows ctx ready finished
    obtain ⟨front,last,eq,remaining,lastDone,earlier,bound⟩ := mixedPages_complete d peers nodes
      result.remaining {result.native.1 with nextPeer := result.native.2.1} nextReady
    refine ⟨result::front,last,?_,remaining,lastDone,?_,?_⟩
    · rw [List.cons_append,← eq]
    · intro page member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · cases isDone : result.native.2.2.2.1
        · rfl
        · exact False.elim (finished (done.mp isDone))
      · exact earlier page member
    · have decreases := mixedPageReady_progress d peers nodes rows ctx ready finished
      change mixedPageMeasure result.remaining {result.native.1 with nextPeer := result.native.2.1} <
        mixedPageMeasure rows ctx at decreases
      change (mixedPages d peers nodes result.remaining
        {result.native.1 with nextPeer := result.native.2.1} nextReady).length + 1 ≤
          mixedPageMeasure rows ctx + 1
      omega
termination_by mixedPageMeasure rows ctx
decreasing_by
  exact mixedPageReady_progress d peers nodes rows ctx ready finished

end Leanux.Proofs.WG.Config
