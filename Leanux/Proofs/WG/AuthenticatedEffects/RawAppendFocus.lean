import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendIndependent

/-! Embed a source-local exact append projection among other raw sending
families. The target's proved writer law accounts for the prior interleaving;
neither result erasure nor datagram-value membership substitutes for it. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.Proofs.Logged

theorem focused_projects (encode : L → E) (decode : E → Option L)
    (select : L → Option F) (outer : E → Option F)
    (matching : ∀ event, outer (encode event) = select event)
    (body : PrefixT L State α) (target : PrefixT F State α)
    (appends : Appends body) (independent : Independent target)
    (projects : ProjectsPrefix select id body target) :
    ProjectsPrefix outer id (focusPrefix encode decode body) target := by
  intro w history
  obtain ⟨suffix,grown⟩ := appends w (history.filterMap decode)
  have whole : runPrefix body w (history.filterMap decode) =
      ((runPrefix body w (history.filterMap decode)).1,history.filterMap decode ++ suffix) :=
    Prod.ext rfl grown
  have projected := projects w (history.filterMap decode)
  rw [independent w _,whole] at projected
  have result := congrArg Prod.fst projected
  have events := congrArg Prod.snd projected
  dsimp only [id] at result
  simp only [List.filterMap_append] at events
  have sameSuffix : (runPrefix target w []).2 = suffix.filterMap select :=
    List.append_cancel_left events
  rw [independent w (history.filterMap outer)]
  change ((runPrefix target w []).1,history.filterMap outer ++ (runPrefix target w []).2) =
    ((runPrefix body w (history.filterMap decode)).1.map (fun (value,v) => (value,v)),
      (history ++ ((runPrefix body w (history.filterMap decode)).2.drop
        (history.filterMap decode).length).map encode).filterMap outer)
  rw [sameSuffix,result,grown,List.drop_left]
  simp only [List.filterMap_append,List.filterMap_map]
  have same : (outer ∘ encode) = select := funext matching
  rw [same]

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
