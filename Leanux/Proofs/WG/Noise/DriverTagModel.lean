import Leanux.Proofs.WG.Noise.TagCoverageModel
import Leanux.Proofs.WG.Lifetimes.Store

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Lifetimes

/-! Model: helper edges retain the old receipt/effect unchanged. Peer creation
has its own actual result and projected allocation effect. Administrative gaps
retain raw tags and may delete peers; those gaps alone do not certify unchanged
allocation identity, including a same-zero-tag overwrite. -/
def peerStampStore (s : Campaign2.Snapshot) : Store PeerId :=
  ⟨s.wg.peerCounter, fun pid => (s.peerAt pid).map Peer.internalId⟩

structure PeerCreateReceipt where
  publicKey : Key
  presharedKey : Option Key
  before : Campaign2.Snapshot
  result : Except Int PeerId
  after : Campaign2.Snapshot

def PeerCreateEffect (r : PeerCreateReceipt) : Prop :=
  peerStampStore r.after = (match r.result with
    | .error _ => peerStampStore r.before
    | .ok pid => (peerStampStore r.before).allocate pid) ∧
  ∀ target, r.after.tagAt target = match r.result with
    | .error _ => r.before.tagAt target
    | .ok pid => if pid = target then some HANDSHAKE_ZEROED else r.before.tagAt target

inductive DriverTagEvent where
  | helper (receipt : TagReceipt)
  | peerCreate (receipt : PeerCreateReceipt)

def DriverTagEvent.before : DriverTagEvent → Campaign2.Snapshot
  | .helper r => r.before
  | .peerCreate r => r.before

def DriverTagEvent.after : DriverTagEvent → Campaign2.Snapshot
  | .helper r => r.after
  | .peerCreate r => r.after

def DriverTagEvent.Effect : DriverTagEvent → Prop
  | .helper r => TagReceiptEffect r
  | .peerCreate r => PeerCreateEffect r

def DriverTagMapCoverage (entry : TagMap) (events : List DriverTagEvent) (final : TagMap) : Prop :=
  match events with
  | [] => TagsRetained entry final
  | event :: rest =>
    TagsRetained entry event.before.tagAt ∧ event.Effect ∧
      DriverTagMapCoverage event.after.tagAt rest final

def DriverTagCoverage (entry : Campaign2.Snapshot) (events : List DriverTagEvent)
    (final : Campaign2.Snapshot) : Prop :=
  DriverTagMapCoverage entry.tagAt events final.tagAt

theorem DriverTagMapCoverage.helper_iff (entry final : TagMap) (receipts : List TagReceipt) :
    DriverTagMapCoverage entry (receipts.map DriverTagEvent.helper) final ↔
      TagCoverage entry receipts final := by
  induction receipts generalizing entry with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, DriverTagMapCoverage, DriverTagEvent.before,
      DriverTagEvent.after, DriverTagEvent.Effect, TagCoverage, ih]

theorem DriverTagMapCoverage.of_tagCoverage {entry final : TagMap} {receipts : List TagReceipt}
    (coverage : TagCoverage entry receipts final) :
    DriverTagMapCoverage entry (receipts.map DriverTagEvent.helper) final :=
  (helper_iff entry final receipts).mpr coverage

theorem DriverTagCoverage.helpers_iff (entry final : Campaign2.Snapshot) (receipts : List TagReceipt) :
    DriverTagCoverage entry (receipts.map DriverTagEvent.helper) final ↔
      TagCoverage entry.tagAt receipts final.tagAt :=
  DriverTagMapCoverage.helper_iff _ _ receipts

theorem DriverTagMapCoverage.initial_retained {a b final : TagMap} {events : List DriverTagEvent}
    (pre : TagsRetained a b) (coverage : DriverTagMapCoverage b events final) :
    DriverTagMapCoverage a events final := by
  cases events with
  | nil => exact pre.trans coverage
  | cons event rest => exact ⟨pre.trans coverage.1,coverage.2⟩

theorem DriverTagMapCoverage.final_retained {entry a b : TagMap} {events : List DriverTagEvent}
    (coverage : DriverTagMapCoverage entry events a) (post : TagsRetained a b) :
    DriverTagMapCoverage entry events b := by
  induction events generalizing entry with
  | nil => exact coverage.trans post
  | cons event rest ih => exact ⟨coverage.1,coverage.2.1,ih coverage.2.2⟩

theorem DriverTagMapCoverage.append {entry middle final : TagMap} {left right : List DriverTagEvent}
    (first : DriverTagMapCoverage entry left middle) (second : DriverTagMapCoverage middle right final) :
    DriverTagMapCoverage entry (left ++ right) final := by
  induction left generalizing entry with
  | nil => exact second.initial_retained first
  | cons event rest ih => exact ⟨first.1,first.2.1,ih first.2.2⟩

theorem DriverTagMapCoverage.receipt {entry : TagMap} {events : List DriverTagEvent}
    (event : DriverTagEvent) (prior : DriverTagMapCoverage entry events event.before.tagAt)
    (effect : event.Effect) :
    DriverTagMapCoverage entry (events ++ [event]) event.after.tagAt :=
  prior.append ⟨TagsRetained.refl _,effect,TagsRetained.refl _⟩

theorem DriverTagMapCoverage.surviving_origin {entry final : TagMap} {events : List DriverTagEvent}
    (coverage : DriverTagMapCoverage entry events final) (pid tag : Nat)
    (present : final pid = some tag) :
    entry pid = some tag ∨ ∃ event ∈ events, event.after.tagAt pid = some tag := by
  induction events generalizing entry with
  | nil => exact Or.inl (coverage pid tag present)
  | cons event rest ih =>
    rcases ih coverage.2.2 with earlier | ⟨e,member,origin⟩
    · exact Or.inr ⟨event,by simp,earlier⟩
    · exact Or.inr ⟨e,List.mem_cons_of_mem _ member,origin⟩

end Leanux.Proofs.WG.Noise
