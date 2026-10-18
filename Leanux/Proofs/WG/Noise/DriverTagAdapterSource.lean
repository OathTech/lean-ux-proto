import Leanux.Proofs.WG.Noise.DriverTagSource
import Leanux.Proofs.WG.Noise.ReceptionCallerClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Origins

/-- The legacy observer executes once with its own empty journal. Its actual
receipt suffix is appended to the incoming mixed journal, including on Stop.
No filtered prior history is substituted for legacy tag coverage. -/
def appendHelpers {α : Type} (action : WGPrefix TagReceipt α) : Obs α :=
  fun g ambient => ExceptT.mk fun history =>
    let out := runWGPrefix action g ambient []
    (out.1, history ++ out.2.map DriverTagEvent.helper)

theorem appendHelpers_run {α : Type} (action : WGPrefix TagReceipt α)
    (g : WGWorld) (ambient : Ambient) (history : List DriverTagEvent) :
    runWGPrefix (appendHelpers action) g ambient history =
      ((runWGPrefix action g ambient []).1,
        history ++ (runWGPrefix action g ambient []).2.map DriverTagEvent.helper) := rfl

theorem appendHelpers_erases {α : Type} (observed : WGPrefix TagReceipt α) (action : WG.M α)
    (erases : ErasesStatePrefix observed action) :
    ErasesStatePrefix (appendHelpers observed) action := by
  intro g ambient history
  exact erases g ambient []

theorem valid_append_helpers (prior : List DriverTagEvent) (receipts : List TagReceipt)
    (hp : ValidHistory prior) (hs : ReceptionCaller.ValidHistory receipts) :
    ValidHistory (prior ++ receipts.map DriverTagEvent.helper) := by
  intro event member
  rcases List.mem_append.mp member with member | member
  · exact hp event member
  · obtain ⟨receipt,inside,equal⟩ := List.mem_map.mp member
    subst event
    exact hs receipt inside

theorem appendHelpers_preserves {α : Type} (entry : TagMap) (observed : WGPrefix TagReceipt α)
    (valid : ∀ g ambient, ReceptionCaller.ValidHistory (runWGPrefix observed g ambient []).2)
    (coverage : ∀ g ambient result final after history,
      runWGPrefix observed g ambient [] = (.ok ((result,final),after),history) →
      TagCoverage (responseTagMap g.dev) history (responseTagMap final.dev)) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (appendHelpers observed) := by
  intro g ambient h prior
  have executed : runPrefix ((appendHelpers observed).run g) ambient h =
      ((runWGPrefix observed g ambient []).1,
        h ++ (runWGPrefix observed g ambient []).2.map DriverTagEvent.helper) := rfl
  rw [executed]
  have safe := valid_append_helpers h _ prior.2 (valid g ambient)
  refine ⟨_,rfl,safe,?_⟩
  cases run : runWGPrefix observed g ambient [] with
  | mk result receipts =>
    cases result with
    | error stop => trivial
    | ok out =>
      obtain ⟨⟨value,final⟩,after⟩ := out
      have segment := DriverTagMapCoverage.of_tagCoverage (coverage g ambient value final after receipts run)
      exact ⟨prior.1.append segment,by simpa only [run] using safe⟩

/-- A returned receipt bundle is appended only after its whole native callback
returns normally. A callback Stop retains the incoming journal unchanged. -/
def completedHelpers {α β : Type} (action : WG.M α) (value : α → β)
    (receipts : α → List TagReceipt) : Obs β :=
  fun g ambient => ExceptT.mk fun history =>
    match (action.run g).run ambient with
    | .error stop => (.error stop,history)
    | .ok ((result,final),after) =>
      (.ok ((value result,final),after),history ++ (receipts result).map DriverTagEvent.helper)

theorem completedHelpers_run {α β : Type} (action : WG.M α) (value : α → β)
    (receipts : α → List TagReceipt) (g : WGWorld) (ambient : Ambient)
    (history : List DriverTagEvent) :
    runPrefix ((completedHelpers action value receipts).run g) ambient history =
      match (action.run g).run ambient with
      | .error stop => (.error stop,history)
      | .ok ((result,final),after) =>
        (.ok ((value result,final),after),history ++ (receipts result).map DriverTagEvent.helper) := rfl

theorem completedHelpers_erases {α β : Type} (action : WG.M α) (value : α → β)
    (receipts : α → List TagReceipt) :
    ErasesStatePrefix (completedHelpers action value receipts)
      (do let result ← action; pure (value result)) := by
  intro g ambient history
  rw [completedHelpers_run]
  change ((match (action.run g).run ambient with
    | .error stop => (.error stop,history)
    | .ok ((result,final),after) =>
      (.ok ((value result,final),after),history ++ (receipts result).map DriverTagEvent.helper)) : Except Stop ((β × WGWorld) × Ambient) × List DriverTagEvent).1 =
    ((action.run g).run ambient >>= fun ((result,final),after) =>
      .ok ((value result,final),after))
  cases (action.run g).run ambient <;> rfl

theorem completedHelpers_preserves {α β : Type} (entry : TagMap)
    (action : WG.M α) (value : α → β) (receipts : α → List TagReceipt)
    (valid : ∀ g ambient result final after,
      (action.run g).run ambient = .ok ((result,final),after) →
      ReceptionCaller.ValidHistory (receipts result))
    (coverage : ∀ g ambient result final after,
      (action.run g).run ambient = .ok ((result,final),after) →
      TagCoverage (responseTagMap g.dev) (receipts result) (responseTagMap final.dev)) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (completedHelpers action value receipts) := by
  intro g ambient h prior
  rw [completedHelpers_run]
  cases run : (action.run g).run ambient with
  | error stop =>
    exact ⟨[],by simp,prior.2,True.intro⟩
  | ok out =>
    obtain ⟨⟨result,final⟩,after⟩ := out
    have safe := valid_append_helpers h _ prior.2 (valid g ambient result final after run)
    have normal := prior.1.append
      (DriverTagMapCoverage.of_tagCoverage (coverage g ambient result final after run))
    exact ⟨_,rfl,safe,normal,safe⟩

end Leanux.Proofs.WG.Noise.DriverTags
