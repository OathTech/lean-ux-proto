import Leanux.Proofs.WG.Noise.TagSequenceModel

/-! Handshake edges separated by caller work that may remove peers. Receipt
edges retain their original effects; administrative gaps cannot invent tags. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

abbrev TagMap := PeerId → Option Nat

def TagsRetained (before after : TagMap) : Prop :=
  ∀ pid tag, after pid = some tag → before pid = some tag

theorem TagsRetained.refl (tags : TagMap) : TagsRetained tags tags :=
  fun _ _ present => present

theorem TagsRetained.trans {a b c : TagMap}
    (first : TagsRetained a b) (second : TagsRetained b c) : TagsRetained a c :=
  fun pid tag present => first pid tag (second pid tag present)

/-- Every tag-changing edge satisfies the named helper effect. Source receipt
validity is a separate obligation. Gaps may delete a peer, but cannot add or
change a surviving tag. -/
def TagCoverage (entry : TagMap) (receipts : List TagReceipt) (final : TagMap) : Prop :=
  match receipts with
  | [] => TagsRetained entry final
  | receipt :: rest =>
    TagsRetained entry receipt.before.tagAt ∧ TagReceiptEffect receipt ∧
      TagCoverage receipt.after.tagAt rest final

theorem TagCoverage.initial_retained {a b final : TagMap} {receipts : List TagReceipt}
    (pre : TagsRetained a b) (coverage : TagCoverage b receipts final) :
    TagCoverage a receipts final := by
  cases receipts with
  | nil => exact pre.trans coverage
  | cons receipt rest => exact ⟨pre.trans coverage.1,coverage.2⟩

theorem TagCoverage.final_retained {entry a b : TagMap} {receipts : List TagReceipt}
    (coverage : TagCoverage entry receipts a) (post : TagsRetained a b) :
    TagCoverage entry receipts b := by
  induction receipts generalizing entry with
  | nil => exact coverage.trans post
  | cons receipt rest ih => exact ⟨coverage.1,coverage.2.1,ih coverage.2.2⟩

theorem TagCoverage.append {entry middle final : TagMap} {left right : List TagReceipt}
    (first : TagCoverage entry left middle) (second : TagCoverage middle right final) :
    TagCoverage entry (left ++ right) final := by
  induction left generalizing entry with
  | nil => exact second.initial_retained first
  | cons receipt rest ih => exact ⟨first.1,first.2.1,ih first.2.2⟩

theorem TagCoverage.receipt {entry : TagMap} {receipts : List TagReceipt}
    (receipt : TagReceipt) (prior : TagCoverage entry receipts receipt.before.tagAt)
    (effect : TagReceiptEffect receipt) :
    TagCoverage entry (receipts ++ [receipt]) receipt.after.tagAt :=
  prior.append ⟨TagsRetained.refl _,effect,TagsRetained.refl _⟩

/-- A surviving final tag comes from the entry or from a checked helper edge. -/
theorem TagCoverage.surviving_origin {entry final : TagMap} {receipts : List TagReceipt}
    (coverage : TagCoverage entry receipts final) (pid tag : Nat)
    (present : final pid = some tag) :
    entry pid = some tag ∨ ∃ receipt ∈ receipts, receipt.after.tagAt pid = some tag := by
  induction receipts generalizing entry with
  | nil => exact Or.inl (coverage pid tag present)
  | cons receipt rest ih =>
    rcases ih coverage.2.2 with earlier | ⟨r,member,origin⟩
    · exact Or.inr ⟨receipt,by simp,earlier⟩
    · exact Or.inr ⟨r,List.mem_cons_of_mem _ member,origin⟩

end Leanux.Proofs.WG.Noise
