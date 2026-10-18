import Leanux.Proofs.WG.Noise.PendingTicketFrames
import Leanux.Proofs.WG.Noise.FreshLifecycleSource
import Leanux.Proofs.WG.Noise.FreshInstallSource
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Keypairs.Frames.WGTransitions
import Leanux.Proofs.WG.Lifetimes.AllocationReleaseFrames
import Leanux.Proofs.WG.Peers.CreationAccess
import Leanux.Proofs.WG.Index.PeerReleaseClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing

def nextSlots (w : WGWorld) (pid : PeerId) : Option KeypairId :=
  (w.dev.bind fun d => d.peers[pid]?).bind Peer.keypairNext

theorem view_slot (w : WGWorld) (pid : PeerId) :
    (view w).slots pid = (nextSlots w pid).bind (keypairResidents w) := by
  cases device : w.dev with
  | none => simp [view,nextSlots,device]
  | some d =>
    cases peer : d.peers[pid]? with
    | none => simp [view,nextSlots,pending,device,peer]
    | some p =>
      cases next : p.keypairNext with
      | none => simp [view,nextSlots,pending,device,peer,next]
      | some kid =>
        cases key : d.keypairs[kid]? <;>
          simp [view,nextSlots,pending,keypairResidents,device,peer,next,key]

theorem next_of_fields (w v : WGWorld) (same : CurrentSlots.fields v = CurrentSlots.fields w) :
    nextSlots v = nextSlots w := by
  funext pid
  have slots := congrFun (congrArg (fun t => t.2.1) same) pid
  have next := congrArg (fun item => item.bind (fun cell => cell.2.2)) slots
  simpa [CurrentSlots.fields,CurrentSlots.slotCell,nextSlots,Option.bind_map,Option.bind_assoc,Function.comp_def] using next

theorem next_of_fresh (w v : WGWorld)
    (same : ∀ pid, freshInstallView pid v.dev = freshInstallView pid w.dev) :
    nextSlots v = nextSlots w := by
  funext pid
  have next := congrArg (fun cell => cell.2.bind id) (same pid)
  simpa [freshInstallView,nextSlots,Option.bind_map,Option.bind_assoc,Function.comp_def] using next

theorem keys_of_snapshot (w v : WGWorld) (same : Keypairs.snapshot v = Keypairs.snapshot w) :
    keypairResidents v = keypairResidents w := by
  funext kid
  have keys := congrFun (congrArg Keypairs.Snapshot.slots same) kid
  have stamps := congrArg (fun item => item.map Keypairs.Cell.stamp) keys
  simpa [Keypairs.snapshot,Keypairs.cell,keypairResidents,Option.map_map,Function.comp_def] using stamps

theorem view_same (w v : WGWorld) (next : nextSlots v = nextSlots w)
    (keys : Keypairs.snapshot v = Keypairs.snapshot w) : view v = view w := by
  apply Store.ext
  · exact congrArg Keypairs.Snapshot.frontier keys
  · funext pid
    rw [view_slot,view_slot,next,keys_of_snapshot w v keys]

theorem view_retained (w v : WGWorld) (counter : v.keypairCounter = w.keypairCounter)
    (next : ResidentsRetained (nextSlots w) (nextSlots v))
    (keys : ResidentsRetained (keypairResidents w) (keypairResidents v)) :
    Retained (view w) (view v) := by
  refine ⟨counter,?_⟩
  intro pid stamp has
  rw [view_slot] at has ⊢
  obtain ⟨kid,hn,hk⟩ := Option.bind_eq_some_iff.mp has
  exact Option.bind_eq_some_iff.mpr ⟨kid,next pid kid hn,keys kid stamp hk⟩

theorem frame_from_fields {α : Type} {a : WG.M α}
    (slots : SameView CurrentSlots.fields a) (keys : Keypairs.SameSnapshot a) :
    SameView view a := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  exact view_same w v
    (next_of_fields w v ((ProjectedAction.iff_run_ambient _ _ _).mp slots w ambient x v after run))
    ((ProjectedAction.iff_run_ambient _ _ _).mp keys w ambient x v after run)

theorem frame_from_fresh {α : Type} {a : WG.M α}
    (slots : ∀ tracked entry, Ensures a (FreshTransport tracked entry)
      (fun _ => FreshTransport tracked entry))
    (keys : Keypairs.SameSnapshot a) : SameView view a := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  apply view_same w v
  · apply next_of_fresh
    intro tracked
    exact slots tracked w.dev w ambient x v after rfl run
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp keys w ambient x v after run

theorem createInitiation_frame (pid : PeerId) : SameView view (createInitiation pid) :=
  frame_from_fresh (createInitiation_spec_freshTransport_variant pid)
    (Keypairs.WGTransitions.createInitiation_sameSnapshot pid)

theorem createResponse_frame (pid : PeerId) : SameView view (createResponse pid) :=
  frame_from_fresh (createResponse_spec_freshTransport_variant pid)
    (Keypairs.WGTransitions.createResponse_sameSnapshot pid)

theorem consumeInitiation_frame (msg : List UInt8) : SameView view (consumeInitiation msg) :=
  frame_from_fresh (consumeInitiation_spec_freshTransport_variant msg)
    (Keypairs.WGTransitions.consumeInitiation_sameSnapshot msg)

theorem consumeResponse_frame (msg : List UInt8) : SameView view (consumeResponse msg) :=
  frame_from_fresh (consumeResponse_spec_freshTransport_variant msg)
    (Keypairs.WGTransitions.consumeResponse_sameSnapshot msg)

theorem handshakeClear_frame (pid : PeerId) : SameView view (handshakeClear pid) :=
  frame_from_fresh (handshakeClear_freshTransport pid)
    (Keypairs.WGTransitions.handshakeClear_sameSnapshot pid)

theorem expireCurrentPeerKeypairs_frame (pid : PeerId) : SameView view (expireCurrentPeerKeypairs pid) :=
  frame_from_fresh (expireCurrentPeerKeypairs_freshTransport pid)
    (Keypairs.WGTransitions.expireCurrentPeerKeypairs_sameSnapshot pid)

theorem dstCacheReset_frame (pid : PeerId) : SameView view (dstCacheReset pid) :=
  frame_from_fields (CurrentSlots.dstCacheReset_fields pid)
    (Keypairs.WGFrames.dstCacheReset_sameSnapshot pid)

theorem handshakeInit_frame (pid : PeerId) (psk : Option Key) : SameView view (handshakeInit pid psk) :=
  frame_from_fields (CurrentSlots.handshakeInit_fields pid psk)
    (Keypairs.WGFrames.handshakeInit_sameSnapshot pid psk)

theorem resetLastSentHandshake_frame (pid : PeerId) : SameView view (resetLastSentHandshake pid) :=
  frame_from_fields (CurrentSlots.resetLastSentHandshake_fields pid)
    (Keypairs.WGFrames.resetLastSentHandshake_sameSnapshot pid)

end Leanux.Proofs.WG.Noise.PendingTickets

namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do

abbrev RetainsCall {α : Type} (a : WG.M α) := ProjectedAction view Retained a

theorem retained_of_frame {α : Type} {a : WG.M α} (same : SameView view a) : RetainsCall a := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  rw [(ProjectedAction.iff_run_ambient _ _ _).mp same w ambient x v after run]
  exact Retained.refl _

theorem retains_bind {α β : Type} {a : WG.M α} {f : α → WG.M β}
    (first : RetainsCall a) (next : ∀ x, RetainsCall (f x)) : RetainsCall (a >>= f) := by
  intro initial
  apply hoare_bind _ _ (first initial)
  intro x
  exact (next x).wp (Retained initial) (fun _ _ later earlier => earlier.trans later)

theorem frame_ambient {α : Type} (a : AmbientM α) :
    SameView view (monadLift a : WG.M α) := fun initial =>
  hoare_liftAmbient a (fun w => view w = initial)

def storeView (s : WGStoreView) : Store PeerId :=
  ⟨s.keypairCounter, fun pid => s.dev.bind fun d => pending d pid⟩

theorem frame_store {α : Type} {a : WG.M α} (same : SameWGStore a) : SameView view a :=
  same.of_factor storeView view (fun _ => rfl)

theorem modifyDev_frame (f : Device → Device)
    (peers : ∀ d, (f d).peers = d.peers) (keys : ∀ d, (f d).keypairs = d.keypairs) :
    SameView view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  cases run
  apply Store.ext
  · rfl
  · funext pid
    simp [view,pending,Option.bind_map,Function.comp_def,peers,keys]

theorem creationCore_view (w : WGWorld) (pid : PeerId) (key : Key) :
    view (Peers.creationCoreWorld w pid key) = (view w).put pid none := by
  apply Store.ext
  · rfl
  · funext tracked
    cases device : w.dev <;> by_cases same : tracked = pid
    all_goals simp [view,pending,Peers.creationCoreWorld,Peers.createdPeer,
      Store.put,device,Std.TreeMap.getElem?_insert,same,Ne.symm]

theorem creationCore_retained (pid : PeerId) (key : Key) :
    RetainsCall (Peers.peerCreateCore pid key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  rw [Peers.peerCreateCore_run] at run
  cases run
  rw [creationCore_view]
  exact erase_retained _ _

theorem creationTail_retained (pid : PeerId) (key : Key) (psk : Option Key) :
    RetainsCall (do
      dstCacheReset pid
      handshakeInit pid psk
      resetLastSentHandshake pid
      modifyDev fun d => { d with peerList := d.peerList ++ [pid], peerHashtable := (key, pid) :: d.peerHashtable, numPeers := d.numPeers + 1 }
      pure (.ok pid : Except Int PeerId)) := by
  apply retains_bind (retained_of_frame (dstCacheReset_frame pid))
  intro _
  apply retains_bind (retained_of_frame (handshakeInit_frame pid psk))
  intro _
  apply retains_bind (retained_of_frame (resetLastSentHandshake_frame pid))
  intro _
  apply retains_bind (retained_of_frame (modifyDev_frame
    (fun d => { d with peerList := d.peerList ++ [pid], peerHashtable := (key, pid) :: d.peerHashtable, numPeers := d.numPeers + 1 })
    (fun _ => rfl) (fun _ => rfl)))
  intro _
  exact retained_of_frame (SameView.pure view _)

theorem peerCreate_retained (key : Key) (psk : Option Key) :
    RetainsCall (peerCreate key psk) := by
  rw [← Peers.peerCreateFactored_eq]
  unfold Peers.peerCreateFactored
  apply retains_bind (retained_of_frame (frame_store getDev_sameWGStore))
  intro d
  apply retains_bind (retained_of_frame (frame_ambient
    (AmbientM.branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE)))
  intro maxed
  cases maxed with
  | true => exact retained_of_frame (SameView.pure view _)
  | false =>
    apply retains_bind (retained_of_frame (frame_ambient (AmbientM.hiddenAlloc .kmemCacheZallocPeer)))
    intro allocated
    apply retains_bind (retained_of_frame (frame_ambient (AmbientM.branch .peerCreateNoMem (!allocated))))
    intro failed
    cases failed with
    | true => exact retained_of_frame (SameView.pure view _)
    | false =>
      apply retains_bind (retained_of_frame (frame_ambient (AmbientM.branch .peerCreateDstCacheFail false)))
      intro failedCache
      cases failedCache with
      | true => exact retained_of_frame (SameView.pure view _)
      | false =>
        apply retains_bind (creationCore_retained d.nextPeer key)
        intro _
        exact creationTail_retained d.nextPeer key psk

theorem keypairPut_retained (kp : Option KeypairId) (now : Bool) :
    RetainsCall (keypairPut kp now) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  have allocation := Lifetimes.keypairPut_retention kp now w v ambient after run
  have peers := ((ensures_iff _ _ _).mpr
    (keypairPut_peers_spec (fun ps => ps = peerAt w) kp now))
    w ambient x v after rfl run
  apply view_retained w v
    (congrArg AllocationMetadata.keyCounter allocation.metadata) _ allocation.key
  intro pid kid has
  change (peerAt v pid).bind Peer.keypairNext = some kid at has
  change (peerAt w pid).bind Peer.keypairNext = some kid
  rwa [peers] at has

theorem releasedPeer_next (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    ResidentsRetained (fun (q : PeerId) => (d.peers[q]?).bind Peer.keypairNext)
      (fun (q : PeerId) => ((Index.releasedPeerDevice d pid p).peers[q]?).bind Peer.keypairNext) := by
  intro tracked kid has
  by_cases last : p.refcount = 1 <;> by_cases same : pid = tracked
  all_goals simp_all [Index.releasedPeerDevice,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase]

theorem peerPut_next (peer : Option PeerId) :
    ProjectedAction nextSlots ResidentsRetained (peerPut peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases peer with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact fun _ _ h => h
  | some pid =>
    cases device : g.dev with
    | none =>
      simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,
        device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,
          device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0
        · simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,
            device,resident,zero,refcountDecAndTest,branchCmp,AmbientM.branchCmp,
            invariant,AmbientM.invariant] at run
          cases run
        · have live : 0 < p.refcount := by omega
          have effect := Index.peerPut_exact pid d p resident live g ambient device
          change (match Index.peerReleaseRefusal pid p with
            | some stop => Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .error stop
            | none => ∃ s, Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) =
              .ok ((), s) ∧ s.wg.device = some (Index.releasedPeerDevice d pid p)) at effect
          rw [run] at effect
          cases refused : Index.peerReleaseRefusal pid p with
          | some stop => simp [refused,Campaign2.observeResult,Except.map] at effect
          | none =>
            simp only [refused,Campaign2.observeResult,Except.map] at effect
            obtain ⟨s,equality,actual⟩ := effect
            cases equality
            change final.dev = some (Index.releasedPeerDevice d pid p) at actual
            simpa [ResidentsRetained,nextSlots,device,actual] using releasedPeer_next d pid p resident

theorem peerPut_retained (peer : Option PeerId) : RetainsCall (peerPut peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  have allocation := Lifetimes.peerPut_retention peer w v ambient after run
  exact view_retained w v (congrArg AllocationMetadata.keyCounter allocation.metadata)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (peerPut_next peer) w ambient x v after run)
    allocation.key

end Leanux.Proofs.WG.Noise.PendingTickets
