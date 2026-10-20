import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAccountMetadataFrames

/-! Namespace exit retains the literal socket and endpoint-maintenance
steps. Peer replacement is tied to the preceding getter, never an arbitrary
saved record supplied by a caller. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AccountMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def listShape (items : List ι) (initial : σ)
    (body : ι → σ → WG.M (ForInStep σ))
    (sources : ∀ item acc,Shape (body item acc)) : Shape (forIn items initial body) :=
  List.rec (motive:=fun values=>∀ acc,Shape (forIn values acc body))
    (fun acc=>.pure acc)
    (fun value rest ih acc=>(List.forIn_cons body value rest acc).symm ▸
      Shape.bind (sources value acc) (fun decision=>match decision with
        | .done final=>.pure final | .yield next=>ih next)) items initial

elab "account_metadata_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a metadata source"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn | Lean.throwError "not a constant source"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("."++name) do
    Lean.throwError "different source head"

macro "account_metadata_step" : tactic => `(tactic| first
  | (account_metadata_head Pure.pure;exact Shape.pure _)
  | (account_metadata_head Bind.bind;apply Shape.bind)
  | (account_metadata_head ForIn.forIn;apply listShape)
  | exact Shape.reading ReadGetter.device
  | exact Shape.reading (ReadGetter.peer _)
  | exact Shape.reading .read
  | exact Shape.ambient _
  | (account_metadata_head modifyDev;apply Shape.write;apply device_view <;> intro d <;> rfl)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

noncomputable def freeShape (sock : Option Nat) : Shape (sockFree sock) := by
  unfold sockFree
  repeat' account_metadata_step

noncomputable def socketShape (new4 new6 : Option Nat) : Shape (socketReinit new4 new6) := by
  unfold socketReinit
  repeat' first | exact freeShape _ | account_metadata_step

noncomputable def resetShape (pid : PeerId) : Shape (dstCacheReset pid) := by
  unfold dstCacheReset
  repeat' first
    | (apply Shape.update;intro p;exact ⟨rfl,rfl,rfl⟩)
    | account_metadata_step

noncomputable def resetNowShape (pid : PeerId) : Shape (dstCacheResetNow pid) := by
  unfold dstCacheResetNow
  apply Shape.bind (resetShape pid)
  intro ignored
  exact .update pid (fun p=>{p with dstCache:={p.dstCache with slot:=none}}) (fun _=>⟨rfl,rfl,rfl⟩)

noncomputable def clearShape (pid : PeerId) : Shape (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc
  rw [←bind_assoc]
  exact .bind (.update pid (fun p=>{p with endpoint:=p.endpoint.map fun e=>{e with src:=0,srcIf:=0}})
    (fun _=>⟨rfl,rfl,rfl⟩)) (fun _=>resetNowShape pid)

noncomputable def preExitShape : Shape netnsPreExit := by
  unfold netnsPreExit
  repeat' first | exact socketShape _ _ | exact clearShape _ | account_metadata_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AccountMetadata
