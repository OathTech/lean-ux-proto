import Leanux.Proofs.WG.Lifetimes.AllocationRetention
import Leanux.Proofs.WG.Keypairs.Ordinary

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Original-call frames for allocation metadata, and reuse of the already
proved keypair ordinary transition. Equal frontiers exclude allocation from
that transition; this fact is independent of the observed event history. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem metadata_modifyDev (f : Device → Device)
    (hf : ∀ d, deviceAllocationMetadata (f d) = deviceAllocationMetadata d) :
    SameView allocationMetadata (modifyDev f) := by
  intro w x v hr
  cases hr
  simp [allocationMetadata, Option.map_map, Function.comp_def, hf]

theorem setPeer_metadata (i : PeerId) (p : Peer) : SameView allocationMetadata (setPeer i p) :=
  metadata_modifyDev _ (fun _ => rfl)

theorem setKeypair_metadata (i : KeypairId) (k : Keypair) : SameView allocationMetadata (setKeypair i k) :=
  metadata_modifyDev _ (fun _ => rfl)

theorem setRxSkb_metadata (i : SkbId) (f : RxPacket → RxPacket) :
    SameView allocationMetadata (setRxSkb i f) := by
  unfold setRxSkb
  apply SameView.bind
  · intro w p v hr
    exact congrArg allocationMetadata (Packets.getRxSkb_current i w v p hr).1
  · intro p; exact metadata_modifyDev _ (fun _ => rfl)

theorem peerGet_metadata (id : PeerId) : SameView allocationMetadata (peerGet id) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, getPeer, getDev, getK, setPeer,
    modifyDev, modifyK, refcountInc, branch, branchCmp, invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [allocationMetadata, deviceAllocationMetadata]

theorem peerPut_metadata (id : Option PeerId) : SameView allocationMetadata (peerPut id) := by
  apply SameView.of_wp
  intro s
  simp only [peerPut, indexRemove_eq, indexUnhash]
  mvcgen [peerPut, requireNotPending, getPeer, getDev, getK, setPeer,
    modifyDev, modifyK, refcountDecAndTest, branch, branchCmp,
    indexRemove, retirePeerUnits, invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [allocationMetadata, deviceAllocationMetadata]
  all_goals subst_vars
  all_goals simp_all [allocationMetadata, deviceAllocationMetadata]

def keypairReleaseRest (w : World) := (Peers.snapshot w, packetResidents w, allocationMetadata w)

theorem keypairPut_rest (kp : Option KeypairId) (now : Bool) :
    SameView keypairReleaseRest (keypairPut kp now) := by
  apply SameView.of_wp
  intro s
  simp only [keypairPut, indexRemove_eq, indexUnhash]
  have hd := fun o k => sameKernel_wp _ (indexOwner_peerDeref_sameKernel o) (fun v => v = k)
  mvcgen [hd, keypairPut, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, branchCmp, refcountDecAndTest, unsupported, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold keypairReleaseRest Peers.snapshot packetResidents allocationMetadata at *
  all_goals simp_all [deviceAllocationMetadata]
  all_goals subst_vars
  all_goals simp_all [deviceAllocationMetadata]

theorem ordinary_same_frontier (ho : Keypairs.Ordinary s t) (hf : t.frontier = s.frontier) :
    ∀ i c, t.slots i = some c → s.slots i = some c := by
  induction ho with
  | refl => exact fun _ _ h => h
  | erase s j =>
    intro i c hc
    by_cases he : i = j
    · subst i; simp at hc
    · simpa [Keypairs.Snapshot.put, he] using hc
  | empty => intro i c hc; cases hc
  | fresh => simp [Keypairs.Snapshot.fresh] at hf
  | @trans s t u first second ih₁ ih₂ =>
    have hf₁ : t.frontier = s.frontier := by
      have := first.frontier_mono; have := second.frontier_mono; omega
    have hf₂ : u.frontier = t.frontier := hf.trans hf₁.symm
    exact fun i c hc => ih₁ hf₁ i c (ih₂ hf₂ i c hc)

theorem keypairPut_retention (kp : Option KeypairId) (now : Bool) (w v : World)
    (hr : (keypairPut kp now).run w = .ok (x, v)) : AllocationRetention w v := by
  have hrest := keypairPut_rest kp now w x v hr
  have hp : Peers.snapshot v = Peers.snapshot w := congrArg Prod.fst hrest
  have ht : packetResidents v = packetResidents w := congrArg (fun s => s.2.1) hrest
  have hm : allocationMetadata v = allocationMetadata w := congrArg (fun s => s.2.2) hrest
  have hf : (Keypairs.snapshot v).frontier = (Keypairs.snapshot w).frontier :=
    congrArg AllocationMetadata.keyCounter hm
  have retained := ordinary_same_frontier (Keypairs.keypairPut_ordinary kp now w x v hr) hf
  refine ⟨hm, hp ▸ Retained.refl _, ?_, fun i stamp hi => ht ▸ hi⟩
  intro i stamp hi
  have projected (q : World) : keypairResidents q i =
      ((Keypairs.snapshot q).slots i).map (·.stamp) := by
    simp [keypairResidents, Keypairs.snapshot, Keypairs.cell, Option.map_map, Function.comp_def]
  rw [projected] at hi
  cases hc : (Keypairs.snapshot v).slots i with
  | none => simp [hc] at hi
  | some c =>
    have old := retained i c hc
    rw [projected, old]
    simpa only [hc] using hi

theorem peerGet_retention (id : PeerId) (w v : World)
    (hr : (peerGet id).run w = .ok (x, v)) : AllocationRetention w v := by
  have rest := peerGet_otherResidents id w x v hr
  have hk : keypairResidents v = keypairResidents w := congrArg Prod.fst rest
  have ht : packetResidents v = packetResidents w := congrArg Prod.snd rest
  exact ⟨peerGet_metadata id w x v hr, Peers.peerGet_retained id w x v hr,
    fun i stamp hi => hk ▸ hi,
    fun i stamp hi => ht ▸ hi⟩

theorem peerPut_retention (id : Option PeerId) (w v : World)
    (hr : (peerPut id).run w = .ok (x, v)) : AllocationRetention w v := by
  have rest := peerPut_otherResidents id w x v hr
  have hk : keypairResidents v = keypairResidents w := congrArg Prod.fst rest
  have ht : packetResidents v = packetResidents w := congrArg Prod.snd rest
  exact ⟨peerPut_metadata id w x v hr, Peers.peerPut_retained id w x v hr,
    fun i stamp hi => hk ▸ hi,
    fun i stamp hi => ht ▸ hi⟩

end Leanux.Proofs.WG.Lifetimes
