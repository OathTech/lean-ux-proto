import Leanux.Proofs.WG.Index.OwnerCoherenceAipRemovalModel
import Leanux.Proofs.WG.Index.AipRemovalFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- The actual saved peer-map walk changes only each peer's allowed-IP list. -/
theorem deleteListedNodes_aipOwnerView (id : NodeId) (d : Device) :
    aipOwnerView (Config.deleteListedNodes id d d.peers.toList) = aipOwnerView d := by
  have outside := Config.deleteListedNodes_withoutPeers id d d.peers.toList
  have table := congrArg Device.indexTable outside
  have keys := congrArg Device.keypairs outside
  have count := congrArg Device.numPeers outside
  have send := congrArg Device.sendWorkQueue outside
  have clear := congrArg Device.clearWorkQueue outside
  simp only [Config.withoutPeers] at table keys count send clear
  unfold aipOwnerView
  rw [table,keys,count,send,clear]
  congr 3
  funext pid
  rw [Config.deleteListedNodes_lookup]
  simp only [Option.map_map]
  rfl

/-- The pointwise observation transports both hashed-owner coherence and the
last-reference slot-coverage obligation, preserving the tracked resident. -/
theorem aipOwnerView_transport (d final : Device) (pid : PeerId) (p : Peer)
    (same : aipOwnerView final = aipOwnerView d)
    (resident : d.peers[pid]? = some p) (coherent : HashedOwnersCoherent d)
    (covered : LastOwnerCovered d pid p) :
    HashedOwnersCoherent final ∧ ∃ q, final.peers[pid]? = some q ∧
      q.refcount = p.refcount ∧ LastOwnerCovered final pid q ∧
      final.numPeers = d.numPeers ∧ final.sendWorkQueue = d.sendWorkQueue ∧
      final.clearWorkQueue = d.clearWorkQueue := by
  have table : final.indexTable = d.indexTable := congrArg Prod.fst same
  have keys : final.keypairs = d.keypairs := congrArg (fun x => x.2.1) same
  have peers : (fun id : PeerId => final.peers[id]?.map aipOwnerPeer) =
      (fun id : PeerId => d.peers[id]?.map aipOwnerPeer) := congrArg (fun x => x.2.2.1) same
  have retained (id : PeerId) (old : Peer) (found : d.peers[id]? = some old) :
      ∃ q, final.peers[id]? = some q ∧ aipOwnerPeer q = aipOwnerPeer old := by
    have observed := congrFun peers id
    rw [found] at observed
    cases actual : final.peers[id]? with
    | none => simp [actual] at observed
    | some q => exact ⟨q,rfl,by simpa [actual] using observed⟩
  have word (owner : IndexOwner) : ownerWord final owner = ownerWord d owner := by
    cases owner with
    | keypair id => simp only [ownerWord,keys]
    | handshake id =>
      have observed := congrArg (Option.map Peer.handshakeEntryPeer) (congrFun peers id)
      simpa [Option.map_map,Function.comp_def,aipOwnerPeer,ownerWord] using observed
  have safe : HashedOwnersCoherent final := by
    intro e member
    obtain ⟨owner,old,stored,found,live,kind⟩ := coherent e (table ▸ member)
    obtain ⟨q,current,masked⟩ := retained owner old found
    have count : q.refcount = old.refcount := by
      simpa only [aipOwnerPeer] using congrArg Peer.refcount masked
    refine ⟨owner,q,(word e.owner).trans stored,current,count ▸ live,?_⟩
    cases shape : e.owner with
    | handshake own => simpa only [shape] using kind
    | keypair id => simpa only [shape,keys] using kind
  obtain ⟨q,current,masked⟩ := retained pid p resident
  have count : q.refcount = p.refcount := by
    simpa only [aipOwnerPeer] using congrArg Peer.refcount masked
  have slots : clearKeys q = clearKeys p := by
    simpa only [aipOwnerPeer,clearKeys] using congrArg clearKeys masked
  refine ⟨safe,q,current,count,?_,congrArg (fun x => x.2.2.2.1) same,
    congrArg (fun x => x.2.2.2.2.1) same,congrArg (fun x => x.2.2.2.2.2) same⟩
  intro last e member stored
  rcases covered (count ▸ last) e (table ▸ member) ((word e.owner).symm.trans stored) with
    hand | ⟨id,owner,listed⟩
  · exact Or.inl hand
  · exact Or.inr ⟨id,owner,slots ▸ listed⟩

/-- Local richer-observation variant of C1 WGBase.listDel_spec, using the
actual saved traversal and guarded device access without a residency premise. -/
theorem listDel_spec_aipOwner_variant (id : NodeId) (initial : Option _) :
    Ensures (listDel id) (fun g => g.dev.map aipOwnerView = initial)
      (fun _ g => g.dev.map aipOwnerView = initial) := by
  intro g ambient value final after pre run
  cases device : g.dev with
  | none =>
    simp [Config.listDel_source,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    obtain ⟨value,next,inputs,executed,effect⟩ := Config.listDel_returns id d g ambient device
    rw [executed] at run
    cases run
    simpa [effect,device,deleteListedNodes_aipOwnerView] using pre

/-- Local richer-observation variant of C1 WGBase.removeByPeer_spec. Actual
trie errors remain possible; no node shape or completion premise is assumed. -/
theorem removeByPeer_spec_aipOwner_variant (pid : PeerId)
    (initial : Option _) :
    Ensures (removeByPeer pid)
      (fun g => g.dev.map aipOwnerView = initial)
      (fun _ g => g.dev.map aipOwnerView = initial) := by
  let P := fun g : WGWorld => g.dev.map aipOwnerView = initial
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
    exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have haip {α : Type} (action : AipM α) :
      Ensures (liftM action : WG.M α) P (fun _ => P) := by
    change Ensures (liftAip action) P (fun _ => P)
    apply (ensures_iff _ _ _).mpr (hoare_liftAip_variant action P ?_)
    intro g d store pre device
    simpa [P, device, aipOwnerView] using pre
  have hpeer (id : PeerId) : Ensures (getPeer id) P (fun _ => P) := by
    intro g a result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec id P) g a result final after pre run).1
  have hmodify (f : Device → Device)
      (same : ∀ d, aipOwnerView (f d) = aipOwnerView d) :
      Ensures (modifyDev f) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
    simpa [P, modifyDev, Option.map_map, Function.comp_def, same] using pre
  have hlistDel (id : NodeId) : Ensures (listDel id) P (fun _ => P) :=
    listDel_spec_aipOwner_variant id initial
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    hambient (AmbientM.branch site value)
  have hbit (n : AipNode) (bit : Nat) : Ensures (n.bitAt bit : WG.M (Option NodeId)) P (fun _ => P) := by
    unfold AipNode.bitAt
    split
    · exact hpure _
    · exact hambient (AmbientM.invariant _)
  have hinv {α : Type} (what : String) : Ensures (invariant what : WG.M α) P (fun _ => P) :=
    hambient (AmbientM.invariant what)
  have hnode (id : NodeId) (n : AipNode) :
      Ensures (Config.removeNodeSource id n) P (fun _ => P) := by
    unfold Config.removeNodeSource
    repeat' first
      | (with_reducible exact hpure _)
      | (with_reducible exact haip _)
      | (with_reducible exact hbit _ _)
      | (with_reducible exact hbranch _ _)
      | (with_reducible exact hinv _)
      | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | split
  have hlist {α β : Type} (xs : List α) (initial : β)
      (body : α → β → WG.M (ForInStep β))
      (step : ∀ a b, Ensures (body a b) P (fun _ => P)) :
      Ensures (forIn xs initial body) P (fun _ => P) := by
    induction xs generalizing initial with
    | nil => simpa only [List.forIn_nil] using hpure initial
    | cons x xs ih =>
      rw [List.forIn_cons]
      refine ensures_bind _ _ (step x initial) ?_
      intro result
      cases result with
      | done final => exact hpure final
      | yield next => exact ih next
  rw [Config.removeByPeer_source]
  refine ensures_bind (Q := fun _ => P) _ _ (hpeer pid) ?_
  intro p
  rw [Config.removeByPeer_factor]
  unfold Config.removeByPeerFactored
  refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
  intro empty
  cases empty with
  | true => exact hpure ()
  | false =>
    refine ensures_bind (Q := fun _ => P) _ _ (hmodify _ (fun _ => rfl)) ?_
    intro _
    refine ensures_bind (Q := fun _ => P) _ _ (hlist _ _ _ ?_) ?_
    · intro id accumulator
      refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
      intro _
      refine ensures_bind (Q := fun _ => P) _ _ (hlistDel id) ?_
      intro _
      refine ensures_bind (Q := fun _ => P) _ _ (haip (getNode id)) ?_
      exact hnode id
    · intro _
      refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
      intro _
      exact hpure ()

end Leanux.Proofs.WG.Index
