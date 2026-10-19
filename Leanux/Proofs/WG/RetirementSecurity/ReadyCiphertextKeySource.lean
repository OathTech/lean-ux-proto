import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextStagingFrames

/-! The native nonce loop preserves older ready batches while assembling
new packets. Allocation and submission discharge their separate physical
freshness obligations at the actual source cut. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits
theorem key_source (locals : List TxLocalBatch) (pid kid : Nat)
    (packets : List WG.Packet) :
    Hoare (stagedKeySource pid kid packets) (Ready locals) (fun _ => Inv) := by
  let P := Ready locals
  have getter := ready_read_key (locals := locals) kid
  have setter := ready_set_key (locals := locals)
  have expired := fun date =>
    (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp P
  have ecn := fun pkt => (ipTunnelEcnEncap_sameWGWorld pkt).wp P
  have out := ready_no_key (locals := locals) pid packets (some kid)
  have submit := fun data=>submit (locals:=locals) pid kid data
  have weaken {α : Type} (action : WG.M α) (h : Preserves P action) :
      Hoare action P (fun _ => Inv) :=
    hoare_consequence h (fun _ h => h) (fun _ _ h => h.2)
  have step {α β : Type} (action : WG.M α) (f : α → WG.M β)
      (Q : β → WGWorld → Prop) (ha : Preserves P action)
      (hf : ∀ x, Hoare (f x) P Q) : Hoare (action >>= f) P Q := hoare_bind action f ha hf
  unfold stagedKeySource
  change Hoare _ P (fun _ => Inv)
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter)
    | (index_material_head setKeypair; exact setter _ _)
    | (index_material_head branchExpired; exact expired _)
    | (index_material_head ipTunnelEcnEncap; exact ecn _)
    | (index_material_head stagedOutNokey; first | exact out _ | exact weaken _ (out _))
    | (index_material_head stagedSubmit; exact submit _)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | (index_material_head Pure.pure; first | exact preserves_pure _ | exact weaken _ (preserves_pure _))
    | (index_material_head Bind.bind; apply step)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
