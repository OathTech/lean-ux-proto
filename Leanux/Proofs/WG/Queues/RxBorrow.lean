import Leanux.Proofs.Framing.PeerBorrow
import Leanux.Proofs.WG.Lifetimes.AllowedLookupAccess
import Leanux.Proofs.WG.Queues.RxQueueView

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! The adjacent original allowed-IP lookup and peerPut in consumeDataDone.
The source lookup result is retained; normal endpoints restore all semantic
Kernel state, while the existing access observer retains real failed prefixes.
No represented-trie, initial live-reference or ownership premise is imposed. -/
namespace Leanux.Proofs.WG.Queues.RxBorrow
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Std.Do
open PeerBorrow

theorem lookup_spec (root : Option NodeId) (bits key : Nat) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ lookup root bits key
    ⦃⇓? result w => ⌜Borrowed initial result w.k⌝⦄ := by
  have hs := sameKernel_wp _ (Lifetimes.swapEndian_sameKernel bits) (fun k => k = initial)
  have hf := sameKernel_wp _ (Lifetimes.findNode_sameKernel root bits key) (fun k => k = initial)
  have hn := fun id => sameKernel_wp _ (Framing.getNode_sameKernel id) (fun k => k = initial)
  have ha := fun peer => acquire_spec peer initial
  mvcgen [lookup, hs, hf, hn, ha, branch, invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Borrowed]

theorem lookupSrc_spec (protocol : Nat) (bytes : List UInt8) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ lookupSrc protocol bytes
    ⦃⇓? result w => ⌜Borrowed initial result w.k⌝⦄ := by
  have hd := sameKernel_wp _ getDev_sameKernel (fun k => k = initial)
  have hl := fun root bits key => lookup_spec root bits key initial
  mvcgen [lookupSrc, hd, hl, branch]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Borrowed]

theorem lookupDst_spec (family addr : Nat) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ lookupDst family addr
    ⦃⇓? result w => ⌜Borrowed initial result w.k⌝⦄ := by
  have hd := sameKernel_wp _ getDev_sameKernel (fun k => k = initial)
  have hl := fun root bits key => lookup_spec root bits key initial
  mvcgen [lookupDst, hd, hl, branch]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Borrowed]

def repayLookup (action : M (Option PeerId)) : M (Option PeerId) := do
  let result ← action
  peerPut result
  return result

theorem repayLookup_normal (action : M (Option PeerId))
    (ha : ∀ initial, ⦃fun w => ⌜w.k = initial⌝⦄ action
      ⦃⇓? result w => ⌜Borrowed initial result w.k⌝⦄)
    (w v : World) (result : Option PeerId)
    (hr : (repayLookup action).run w = .ok (result, v)) :
    ∃ acquired, action.run w = .ok (result, acquired) ∧
      Borrowed w.k result acquired.k ∧ view v = view w := by
  simp only [repayLookup, StateT.run_bind] at hr
  cases he : action.run w with
  | error e => simp [he] at hr
  | ok out =>
    rcases out with ⟨peer, acquired⟩
    simp only [he, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    cases hp : (peerPut peer).run acquired with
    | error e => simp [hp] at hr
    | ok out =>
      rcases out with ⟨u, final⟩
      simp [hp] at hr
      rcases hr with ⟨rfl, rfl⟩
      have hb := (hoare_iff_triple _ _ _).mpr (ha w.k) w peer acquired rfl he
      exact ⟨acquired, rfl, hb,
        (hoare_iff_triple _ _ _).mpr (repay_spec peer w.k) acquired u final hb hp⟩

theorem repayLookup_frame (action : M (Option PeerId))
    (ha : ∀ initial, ⦃fun w => ⌜w.k = initial⌝⦄ action
      ⦃⇓? result w => ⌜Borrowed initial result w.k⌝⦄) :
    SameView view (repayLookup action) := by
  intro w result v hr
  exact (repayLookup_normal action ha w v result hr).choose_spec.2.2

def source (protocol : Nat) (bytes : List UInt8) : M (Option PeerId) :=
  repayLookup (lookupSrc protocol bytes)

def observed (protocol : Nat) (bytes : List UInt8) : MixedM (Option PeerId) := do
  let result ← lookupSrcPrefix protocol bytes
  peerPutMixed result
  return result

theorem observed_erases (protocol : Nat) (bytes : List UInt8) :
    ErasesPrefix (observed protocol bytes) (source protocol bytes) := by
  exact erasesPrefix_bind (lookupSrcPrefix_erases _ _) (fun result =>
    erasesPrefix_bind (peerPutMixed_erases result) (fun _ => erasesPrefix_pure result))

theorem source_frame (protocol : Nat) (bytes : List UInt8) :
    SameView view (source protocol bytes) :=
  repayLookup_frame _ (lookupSrc_spec protocol bytes)

theorem destination_frame (family addr : Nat) :
    SameView view (repayLookup (lookupDst family addr)) :=
  repayLookup_frame _ (lookupDst_spec family addr)

/-- Existing concrete allocation safety covers every actual access, including
prefixes that Stop before repayment. It is separate from endpoint restoration. -/
theorem observed_preserves (protocol : Nat) (bytes : List UInt8) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (observed protocol bytes) := by
  unfold observed
  apply PrefixPreserves.bind (AmbientContracts.drop (lookupSrcPrefix_spec allocationAmbient (fun _ => True) _ _))
  intro result
  apply PrefixPreserves.bind (allocationAmbient.peerPut result)
  intro u
  exact PrefixPreserves.pure (fun _ _ hi => hi.safe) result

def queuesOfView (s : Kernel × (PeerId → Option Peer)) : PeerId → Option RxQueueCell :=
  fun pid => s.1.wg.bind fun d => (s.2 pid).map fun p => ⟨d.ifindex, p.internalId, p.rxQueue⟩

theorem queues_factor (w : World) : rxQueues w = queuesOfView (view w) := by
  funext pid
  cases hd : w.k.wg <;> simp [rxQueues, rxMap, queuesOfView, view, outsidePeers, resident, hd]

theorem source_queues (protocol : Nat) (bytes : List UInt8) :
    SameView rxQueues (source protocol bytes) :=
  (source_frame protocol bytes).of_factor queuesOfView rxQueues queues_factor

/-- Complete peer equality gives both NAPI and all three key slots, including
arbitrary duplicated slot IDs. No slot or keypair residency is assumed. -/
theorem source_peer_fields (protocol : Nat) (bytes : List UInt8) (pid : PeerId) :
    SameView (fun w => (resident w.k pid).map fun p =>
      (p.napiScheduled, p.keypairCurrent, p.keypairPrevious, p.keypairNext))
      (source protocol bytes) := by
  exact (source_frame protocol bytes).factor (fun s => (s.2 pid).map fun p =>
    (p.napiScheduled, p.keypairCurrent, p.keypairPrevious, p.keypairNext))

/-- A key reference is below the current allocation frontier and any resident
key at that slot belongs to the named peer. Existence is not required. -/
def KeyRef (d : Device) (pid : PeerId) (kid : KeypairId) : Prop :=
  kid < d.nextKeypairId ∧ ∀ key, d.keypairs[kid]? = some key → key.peer = some pid

def SlotAffiliation (w : World) : Prop :=
  ∀ d pid p kid, w.k.wg = some d → d.peers[pid]? = some p →
    (p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid) →
    KeyRef d pid kid

def affiliationOfView (s : Kernel × (PeerId → Option Peer)) : Prop :=
  ∀ d pid p kid, s.1.wg = some d → s.2 pid = some p →
    (p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid) →
    KeyRef d pid kid

theorem affiliation_factor (w : World) : SlotAffiliation w = affiliationOfView (view w) := by
  apply propext
  cases hd : w.k.wg with
  | none => simp [SlotAffiliation, affiliationOfView, view, outsidePeers, resident, hd]
  | some d =>
    simp only [SlotAffiliation, affiliationOfView, view, outsidePeers, resident,
      hd, Option.map_some, Option.bind_some, Option.some.injEq]
    constructor
    · intro h d' pid p kid he hp hs
      subst d'
      exact h d pid p kid rfl hp hs
    · intro h d' pid p kid he hp hs
      subst d'
      exact h {d with peers := {}} pid p kid rfl hp hs

/-- This local cut preserves an affiliation invariant if one already holds;
initialization and the other pipeline transitions are not asserted here. -/
theorem source_affiliation (protocol : Nat) (bytes : List UInt8) :
    SameView SlotAffiliation (source protocol bytes) :=
  (source_frame protocol bytes).of_factor affiliationOfView SlotAffiliation affiliation_factor

end Leanux.Proofs.WG.Queues.RxBorrow
