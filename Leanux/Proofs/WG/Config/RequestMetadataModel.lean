import Leanux.Proofs.WG.Config.RequestOrderModel
import Leanux.Proofs.WG.Config.GetterMetadataModel

/-! Metadata at completed key-stage and peer-command cuts. Normal outcomes expose a final value; Stops only retain receipt consistency. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

def metadataValues (r : Receipt) : List GetterMetadata :=
  match r.kind with
  | .keyStage => [getterMetadataObservation r.after]
  | .peer _ => [getterMetadataObservation r.before,getterMetadataObservation r.after]
  | _ => []

def MetadataAll (h : List Receipt) (metadata : GetterMetadata) : Prop :=
  ∀ r ∈ h, ∀ value ∈ metadataValues r, value=metadata

def MetadataConsistent (h : List Receipt) : Prop := ∃ metadata,MetadataAll h metadata
def NoMetadata (h : List Receipt) : Prop := ∀ r ∈ h,metadataValues r=[]

def MetadataFacts (result : Inspection) : Prop :=
  MetadataConsistent result.receipts ∧
    match result.outcome with
    | .error _ => True
    | .ok (_,final) => MetadataAll result.receipts (getterMetadataObservation final)

end Leanux.Proofs.WG.Config.RequestOrder
