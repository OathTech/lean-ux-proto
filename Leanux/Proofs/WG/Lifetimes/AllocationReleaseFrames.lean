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
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  simp [allocationMetadata, Option.map_map, Function.comp_def, hf]

theorem setPeer_metadata (i : PeerId) (p : Peer) : SameView allocationMetadata (setPeer i p) :=
  metadata_modifyDev _ (fun _ => rfl)

theorem setKeypair_metadata (i : KeypairId) (k : Keypair) : SameView allocationMetadata (setKeypair i k) :=
  metadata_modifyDev _ (fun _ => rfl)

theorem setRxSkb_metadata (i : SkbId) (f : RxPacket → RxPacket) :
    SameView allocationMetadata (setRxSkb i f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  cases hd : w.dev with
  | none => simp [setRxSkb, liftSkb_run, hd] at hr
  | some d =>
    cases hp : d.rxSkbs[i]? with
    | none =>
      simp [setRxSkb, liftSkb_run, SkbStore.setRx, SkbStore.getRx,
        hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      rw [Packets.setRxSkb_run w ambient d i p f hd hp] at hr
      cases hr
      simp [allocationMetadata, deviceAllocationMetadata, Packets.update, hd]

theorem peerGet_metadata (id : PeerId) : SameView allocationMetadata (peerGet id) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, getPeer, getDev, setPeer,
    modifyDev, refcountInc, branch, branchCmp, invariant, unsupported,
    AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [allocationMetadata, deviceAllocationMetadata]

theorem peerPut_metadata (id : Option PeerId) : SameView allocationMetadata (peerPut id) := by
  apply SameView.of_wp
  intro s
  have index_spec (a : IndexM Unit) :
      Hoare (MonadLift.monadLift a : WG.M Unit)
        (fun w => allocationMetadata w = s) (fun _ w => allocationMetadata w = s) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    have same : allocationMetadata {w with dev := some {d with indexTable := table}} =
        allocationMetadata w := by
      simp only [allocationMetadata, hd, Option.map_some, deviceAllocationMetadata]
    exact same.trans hi
  unfold Hoare at index_spec
  mvcgen [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
    refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    index_spec, retirePeerUnits, modifyAmbient, invariant, unsupported,
    AmbientM.invariant, AmbientM.unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [allocationMetadata, deviceAllocationMetadata]
  all_goals subst_vars
  all_goals simp_all [deviceAllocationMetadata]

def keypairReleaseRest (w : WGWorld) := (Peers.snapshot w, packetResidents w, allocationMetadata w)

theorem keypairPut_rest (kp : Option KeypairId) (now : Bool) :
    SameView keypairReleaseRest (keypairPut kp now) := by
  apply SameView.of_wp
  intro s
  have hd := fun o => indexOwner_peerDeref_preserves o (fun w => keypairReleaseRest w = s)
  have index_spec (a : IndexM Unit) :
      Hoare (MonadLift.monadLift a : WG.M Unit)
        (fun w => keypairReleaseRest w = s) (fun _ w => keypairReleaseRest w = s) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    have same : keypairReleaseRest {w with dev := some {d with indexTable := table}} =
        keypairReleaseRest w := by
      unfold keypairReleaseRest Peers.snapshot packetResidents allocationMetadata
      simp only [hd, Option.bind_some, Option.map_some, deviceAllocationMetadata]
    exact same.trans hi
  unfold Preserves Hoare at hd
  unfold Hoare at index_spec
  mvcgen [hd, index_spec, keypairPut, getKeypair, getDev, setKeypair, modifyDev,
    branch, branchCmp, refcountDecAndTest, unsupported, invariant,
    AmbientM.branch, AmbientM.branchCmp, AmbientM.unsupported, AmbientM.invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold keypairReleaseRest Peers.snapshot packetResidents allocationMetadata at *
  all_goals simp_all [deviceAllocationMetadata, Option.bind_map, Function.comp_def]
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

theorem keypairPut_retention (kp : Option KeypairId) (now : Bool) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((keypairPut kp now).run w).run ambient = .ok ((x, v), ambient')) : AllocationRetention w v := by
  have hrest := (ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_rest kp now) w ambient x v ambient' hr
  have hp : Peers.snapshot v = Peers.snapshot w := congrArg Prod.fst hrest
  have ht : packetResidents v = packetResidents w := congrArg (fun s => s.2.1) hrest
  have hm : allocationMetadata v = allocationMetadata w := congrArg (fun s => s.2.2) hrest
  have hf : (Keypairs.snapshot v).frontier = (Keypairs.snapshot w).frontier :=
    congrArg AllocationMetadata.keyCounter hm
  have retained := ordinary_same_frontier ((ProjectedAction.iff_run_ambient _ _ _).mp
    (Keypairs.keypairPut_ordinary kp now) w ambient x v ambient' hr) hf
  refine ⟨hm, hp ▸ Retained.refl _, ?_, fun i stamp hi => ht ▸ hi⟩
  intro i stamp hi
  have projected (q : WGWorld) : keypairResidents q i =
      ((Keypairs.snapshot q).slots i).map (·.stamp) := by
    simp [keypairResidents, Keypairs.snapshot, Keypairs.cell, Option.map_map, Function.comp_def]
  rw [projected] at hi
  cases hc : (Keypairs.snapshot v).slots i with
  | none => simp [hc] at hi
  | some c =>
    have old := retained i c hc
    rw [projected, old]
    simpa only [hc] using hi

theorem peerGet_retention (id : PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((peerGet id).run w).run ambient = .ok ((x, v), ambient')) : AllocationRetention w v := by
  have rest := (ProjectedAction.iff_run_ambient _ _ _).mp
    (peerGet_otherResidents id) w ambient x v ambient' hr
  have hk : keypairResidents v = keypairResidents w := congrArg Prod.fst rest
  have ht : packetResidents v = packetResidents w := congrArg Prod.snd rest
  exact ⟨(ProjectedAction.iff_run_ambient _ _ _).mp (peerGet_metadata id) w ambient x v ambient' hr,
    (ProjectedAction.iff_run_ambient _ _ _).mp (Peers.peerGet_retained id) w ambient x v ambient' hr,
    fun i stamp hi => hk ▸ hi,
    fun i stamp hi => ht ▸ hi⟩

theorem peerPut_retention (id : Option PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((peerPut id).run w).run ambient = .ok ((x, v), ambient')) : AllocationRetention w v := by
  have rest := (ProjectedAction.iff_run_ambient _ _ _).mp
    (peerPut_otherResidents id) w ambient x v ambient' hr
  have hk : keypairResidents v = keypairResidents w := congrArg Prod.fst rest
  have ht : packetResidents v = packetResidents w := congrArg Prod.snd rest
  exact ⟨(ProjectedAction.iff_run_ambient _ _ _).mp (peerPut_metadata id) w ambient x v ambient' hr,
    (ProjectedAction.iff_run_ambient _ _ _).mp (Peers.peerPut_retained id) w ambient x v ambient' hr,
    fun i stamp hi => hk ▸ hi,
    fun i stamp hi => ht ▸ hi⟩

end Leanux.Proofs.WG.Lifetimes
