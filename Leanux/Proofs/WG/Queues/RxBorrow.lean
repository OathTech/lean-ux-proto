import Leanux.Proofs.WG.Keypairs.Frames.WGMore
import Leanux.Proofs.Framing.PeerBorrow
import Leanux.Proofs.Framing.Product
import Leanux.Proofs.WG.Lifetimes.AllowedLookupAccess
import Leanux.Proofs.WG.Queues.RxQueueView

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! The adjacent original allowed-IP lookup and peerPut in consumeDataDone.
The source lookup result is retained; normal native endpoints restore the
seven WG store observations, while product helpers retain the original 43-field
observation. The existing access observer retains real failed prefixes.
No represented-trie, initial live-reference or ownership premise is imposed. -/
namespace Leanux.Proofs.WG.Queues.RxBorrow
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Std.Do
open PeerBorrow

theorem lookup_spec (root : Option NodeId) (bits key : Nat) (initial : WGStoreView) :
    ⦃fun w => ⌜wgStoreView w = initial⌝⦄ lookup root bits key
    ⦃⇓? result w => ⌜Borrowed initial result (wgStoreView w)⌝⦄ := by
  have hs := (Lifetimes.swapEndian_sameWGStore bits).wp (fun k => k = initial)
  have readAip {α : Type} (a : AipM α) (h : SameView (fun s : AipStore => s) a) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => wgStoreView w = initial) (fun _ w => wgStoreView w = initial) := by
    apply hoare_liftAip_of a
    intro g d hg hd
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro s ambient x s' ambient' he hr
    have hs := (ProjectedAction.iff_run_ambient _ _ _).mp h s ambient x s' ambient' hr
    rw [hs, he]
    simpa [wgStoreView, hd] using hg
  have hf := readAip _ (Lifetimes.findNode_sameAipStore root bits key)
  have hn := fun id => readAip _ (Framing.getNode_sameAipStore id)
  unfold Hoare at hf hn
  have ha := fun peer => acquire_spec peer initial
  mvcgen [lookup, hs, hf, hn, ha, branch, AmbientM.branch,
    invariant, AmbientM.invariant, unsupported, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Borrowed]

theorem lookupSrc_spec (protocol : Nat) (bytes : List UInt8) (initial : WGStoreView) :
    ⦃fun w => ⌜wgStoreView w = initial⌝⦄ lookupSrc protocol bytes
    ⦃⇓? result w => ⌜Borrowed initial result (wgStoreView w)⌝⦄ := by
  have hl := fun root bits key => lookup_spec root bits key initial
  mvcgen [lookupSrc, hl, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Borrowed]

theorem lookupDst_spec (family addr : Nat) (initial : WGStoreView) :
    ⦃fun w => ⌜wgStoreView w = initial⌝⦄ lookupDst family addr
    ⦃⇓? result w => ⌜Borrowed initial result (wgStoreView w)⌝⦄ := by
  have hl := fun root bits key => lookup_spec root bits key initial
  mvcgen [lookupDst, hl, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Borrowed]

def repayLookup {m : Type → Type} [Monad m] [MonadLiftT WG.M m]
    (action : m (Option PeerId)) : m (Option PeerId) := do
  let result ← action
  monadLift (peerPut result)
  return result

theorem repayLookup_normal (action : WG.M (Option PeerId))
    (ha : ∀ initial, ⦃fun w => ⌜wgStoreView w = initial⌝⦄ action
      ⦃⇓? result w => ⌜Borrowed initial result (wgStoreView w)⌝⦄)
    (w v : WGWorld) (ambient ambient' : Ambient) (result : Option PeerId)
    (hr : ((repayLookup action).run w).run ambient = .ok ((result, v), ambient')) :
    ∃ acquired acquiredAmbient, ((action.run w).run ambient = .ok ((result, acquired), acquiredAmbient)) ∧
      Borrowed (wgStoreView w) result (wgStoreView acquired) ∧ view v = view w := by
  simp only [repayLookup, monadLift_self, StateT.run_bind] at hr
  cases he : (action.run w).run ambient with
  | error e => simp [he] at hr
  | ok out =>
    rcases out with ⟨⟨peer, acquired⟩, acquiredAmbient⟩
    simp only [he, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    cases hp : ((peerPut peer).run acquired).run acquiredAmbient with
    | error e => simp [hp] at hr
    | ok out =>
      rcases out with ⟨⟨u, final⟩, finalAmbient⟩
      simp [hp] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      have hb := (hoare_iff_run_ambient _ _ _).mp (ha (wgStoreView w)) w ambient peer acquired acquiredAmbient rfl he
      exact ⟨acquired, acquiredAmbient, rfl, hb,
        (hoare_iff_run_ambient _ _ _).mp (repay_spec peer (wgStoreView w))
          acquired acquiredAmbient u final finalAmbient hb hp⟩

theorem repayLookup_frame (action : WG.M (Option PeerId))
    (ha : ∀ initial, ⦃fun w => ⌜wgStoreView w = initial⌝⦄ action
      ⦃⇓? result w => ⌜Borrowed initial result (wgStoreView w)⌝⦄) :
    SameView view (repayLookup action) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  obtain ⟨acquired, acquiredAmbient, _, _, hf⟩ :=
    repayLookup_normal action ha w v ambient ambient' result hr
  exact hf

/-- The arbitrary product-action contract keeps every former non-WG Kernel
observation as well as the seven WG stores. These are pure projections only. -/
def ProductBorrowed (initial : ProductStore43) (result : Option PeerId)
    (current : ProductStore43) : Prop :=
  current.1 = initial.1 ∧ current.2.1 = initial.2.1 ∧
  current.2.2.1 = initial.2.2.1 ∧ Borrowed initial.2.2.2 result current.2.2.2

def productView (w : World) :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter), view w.wg)

theorem repayLookup_normal_product (action : Leanux.M (Option PeerId))
    (ha : ∀ initial, ⦃fun w => ⌜productStoreView w = initial⌝⦄ action
      ⦃⇓? result w => ⌜ProductBorrowed initial result (productStoreView w)⌝⦄)
    (w v : World) (result : Option PeerId)
    (hr : (repayLookup action).run w = .ok (result, v)) :
    ∃ acquired, action.run w = .ok (result, acquired) ∧
      ProductBorrowed (productStoreView w) result (productStoreView acquired) ∧
      productView v = productView w := by
  simp only [repayLookup, StateT.run_bind] at hr
  cases he : action.run w with
  | error e => simp [he] at hr
  | ok out =>
    rcases out with ⟨peer, acquired⟩
    simp only [he, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    change ((liftWG (peerPut peer)).run acquired >>= fun (u, final) =>
      Except.ok (peer, final)) = _ at hr
    rw [liftWG_run] at hr
    cases hp : ((peerPut peer).run acquired.wg).run acquired.ambient with
    | error e => simp [hp, Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨u, final⟩, finalAmbient⟩
      simp [hp, Except.map] at hr
      rcases hr with ⟨rfl, rfl⟩
      have hb := (hoare_iff_run _ _ _).mp (ha (productStoreView w)) w peer acquired rfl he
      have hv := (hoare_iff_run_ambient _ _ _).mp
        (repay_spec peer (wgStoreView w.wg))
        acquired.wg acquired.ambient u final finalAmbient hb.2.2.2 hp
      refine ⟨acquired, rfl, hb, ?_⟩
      exact Prod.ext hb.1 (Prod.ext hb.2.1 (Prod.ext hb.2.2.1 hv))

theorem repayLookup_frame_product (action : Leanux.M (Option PeerId))
    (ha : ∀ initial, ⦃fun w => ⌜productStoreView w = initial⌝⦄ action
      ⦃⇓? result w => ⌜ProductBorrowed initial result (productStoreView w)⌝⦄) :
    SameView productView (repayLookup action) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v hr
  exact (repayLookup_normal_product action ha w v result hr).choose_spec.2.2

def source (protocol : Nat) (bytes : List UInt8) : WG.M (Option PeerId) :=
  repayLookup (lookupSrc protocol bytes)

def observed (protocol : Nat) (bytes : List UInt8) : MixedM (Option PeerId) := do
  let result ← lookupSrcPrefix protocol bytes
  peerPutMixed result
  return result

theorem observed_erases (protocol : Nat) (bytes : List UInt8) :
    ErasesStatePrefix (observed protocol bytes) (source protocol bytes) := by
  exact erasesStatePrefix_bind (lookupSrcPrefix_erases _ _) (fun result =>
    erasesStatePrefix_bind (peerPutMixed_erases result) (fun _ => erasesStatePrefix_pure result))

theorem source_frame (protocol : Nat) (bytes : List UInt8) :
    SameView view (source protocol bytes) :=
  repayLookup_frame _ (lookupSrc_spec protocol bytes)

theorem destination_frame (family addr : Nat) :
    SameView view (repayLookup (lookupDst family addr)) :=
  repayLookup_frame _ (lookupDst_spec family addr)

/-- Existing concrete allocation safety covers every actual access, including
prefixes that Stop before repayment. It is separate from endpoint restoration. -/
theorem observed_preserves (protocol : Nat) (bytes : List UInt8) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (observed protocol bytes) := by
  unfold observed
  apply StatePrefixEnsures.bind (AmbientContracts.drop (lookupSrcPrefix_spec allocationAmbient (fun _ => True) _ _))
  intro result
  apply StatePrefixEnsures.bind (allocationAmbient.peerPut result)
  intro u
  exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)

def queuesOfView (s : WGStoreView × (PeerId → Option Peer)) : PeerId → Option RxQueueCell :=
  fun pid => s.1.dev.bind fun d => (s.2 pid).map fun p => ⟨d.ifindex, p.internalId, p.rxQueue⟩

theorem queues_factor (w : WGWorld) : rxQueues w = queuesOfView (view w) := by
  funext pid
  cases hd : w.dev <;> simp [rxQueues, rxMap, queuesOfView, view, outsidePeers, resident, wgStoreView, hd]

theorem source_queues (protocol : Nat) (bytes : List UInt8) :
    SameView rxQueues (source protocol bytes) :=
  (source_frame protocol bytes).of_factor queuesOfView rxQueues queues_factor

/-- Complete peer equality gives both NAPI and all three key slots, including
arbitrary duplicated slot IDs. No slot or keypair residency is assumed. -/
theorem source_peer_fields (protocol : Nat) (bytes : List UInt8) (pid : PeerId) :
    SameView (fun w => (resident (wgStoreView w) pid).map fun p =>
      (p.napiScheduled, p.keypairCurrent, p.keypairPrevious, p.keypairNext))
      (source protocol bytes) := by
  exact (source_frame protocol bytes).factor (fun s => (s.2 pid).map fun p =>
    (p.napiScheduled, p.keypairCurrent, p.keypairPrevious, p.keypairNext))

/-- A key reference is below the current allocation frontier and any resident
key at that slot belongs to the named peer. Existence is not required. -/
def KeyRef (d : Device) (pid : PeerId) (kid : KeypairId) : Prop :=
  kid < d.nextKeypairId ∧ ∀ key, d.keypairs[kid]? = some key → key.peer = some pid

def SlotAffiliation (w : WGWorld) : Prop :=
  ∀ d pid p kid, w.dev = some d → d.peers[pid]? = some p →
    (p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid) →
    KeyRef d pid kid

def affiliationOfView (s : WGStoreView × (PeerId → Option Peer)) : Prop :=
  ∀ d pid p kid, s.1.dev = some d → s.2 pid = some p →
    (p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid) →
    KeyRef d pid kid

theorem affiliation_factor (w : WGWorld) : SlotAffiliation w = affiliationOfView (view w) := by
  apply propext
  cases hd : w.dev with
  | none => simp [SlotAffiliation, affiliationOfView, view, outsidePeers, resident, wgStoreView, hd]
  | some d =>
    simp only [SlotAffiliation, affiliationOfView, view, outsidePeers, resident, wgStoreView,
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
