import Leanux.Proofs.WG.Index.StagingRichModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.StagingRich
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem refl (w : WGWorld) : Frame w w :=
  ⟨stagingFrame_refl w,(fun _ h => h),(fun _ _ h => h),(fun _ _ h => h),fun h => h⟩

theorem legacy_trans {a b c : WGWorld} (ab : StagingFrame a b) (bc : StagingFrame b c) :
    StagingFrame a c :=
  ⟨fun h => bc.1 (ab.1 h),fun p t h => ab.2.1 p t (bc.2.1 p t h),bc.2.2.trans ab.2.2⟩

theorem trans {a b c : WGWorld} (ab : Frame a b) (bc : Frame b c) : Frame a c :=
  ⟨legacy_trans ab.legacy bc.legacy,fun e h => ab.tables e (bc.tables e h),
    fun p t h => ab.peers p t (bc.peers p t h),fun k t h => ab.keys k t (bc.keys k t h),
    fun h => bc.live (ab.live h)⟩

theorem forget {α : Type} (action : WG.M α)
    (rich : ∀ entry, Ensures action (Frame entry) (fun _ => Frame entry))
    (entry : WGWorld) :
    Ensures action (StagingFrame entry) (fun _ => StagingFrame entry) := by
  intro g a r f b pre run
  exact legacy_trans pre (rich g g a r f b (refl g) run).legacy

theorem of_same {entry g f : WGWorld} (pre : Frame entry g)
    (legacy : StagingFrame entry f) (tab : table f = table g)
    (peer : peerMap f = peerMap g) (key : keyMap f = keyMap g)
    (live : HashedLive g → HashedLive f) : Frame entry f := by
  refine ⟨legacy,?_,?_,?_,fun h => live (pre.live h)⟩
  · intro e member; exact pre.tables e (tab ▸ member)
  · intro p c present; exact pre.peers p c (peer ▸ present)
  · intro k c present; exact pre.keys k c (key ▸ present)

theorem peerMap_write (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]? = some p) (same : PeerCell q = PeerCell p) :
    (fun target : PeerId => (d.peers.insert pid q)[target]?.map PeerCell) =
      (fun target : PeerId => d.peers[target]?.map PeerCell) := by
  funext target
  by_cases eq : pid = target
  · subst target; simp [resident,same]
  · simp [Std.TreeMap.getElem?_insert,eq]

theorem keyMap_write (d : Device) (kid : KeypairId) (p q : Keypair)
    (resident : d.keypairs[kid]? = some p) (same : KeyCell q = KeyCell p) :
    (fun target : KeypairId => (d.keypairs.insert kid q)[target]?.map KeyCell) =
      (fun target : KeypairId => d.keypairs[target]?.map KeyCell) := by
  funext target
  by_cases eq : kid = target
  · subst target; simp [resident,same]
  · simp [Std.TreeMap.getElem?_insert,eq]

theorem peer_legacy {entry : WGWorld} {pid : PeerId} {p : Peer}
    (cell : peerMap entry pid = some (PeerCell p)) :
    stagingPeerMap entry.dev pid = some (stagingPeerCell p) := by
  have h := congrArg (Option.map (fun c => (c.1,c.2.1))) cell
  simpa [peerMap,stagingPeerMap,PeerCell,stagingPeerCell,Option.map_map,Function.comp_def] using h

theorem same_device (entry g f : WGWorld) (pre : Frame entry g)
    (same : f.dev = g.dev) (counter : f.keypairCounter = g.keypairCounter) :
    Frame entry f := by
  apply of_same pre (stagingFrame_of_views entry g f (by rw [same])
    (by rw [same]) counter pre.legacy)
  · simp [table,same]
  · funext pid; simp [peerMap,same]
  · funext kid; simp [keyMap,same]
  · intro live d present
    exact live d (same.symm.trans present)

theorem of_views (entry g f : WGWorld)
    (cursor : f.dev.map TimerDiscipline.tableCursor = g.dev.map TimerDiscipline.tableCursor)
    (peers : peerMap f = peerMap g) (keys : keyMap f = keyMap g)
    (counter : f.keypairCounter = g.keypairCounter) (pre : Frame entry g) :
    Frame entry f := by
  have tabs : table f = table g := by
    have mapped := congrArg (Option.map Prod.fst) cursor
    simpa [table,TimerDiscipline.tableCursor,Option.map_map,Function.comp_def] using
      congrArg (fun o => o.getD []) mapped
  have peerOld : stagingPeerMap f.dev = stagingPeerMap g.dev := by
    funext pid
    have h := congrArg (Option.map fun c => (c.1,c.2.1)) (congrFun peers pid)
    simpa [peerMap,stagingPeerMap,PeerCell,stagingPeerCell,Option.map_map,Function.comp_def] using h
  apply of_same pre (stagingFrame_of_views entry g f cursor peerOld counter pre.legacy) tabs peers keys
  intro live final hd e member kid owner
  have oldMember : e ∈ table g := by
    rw [← tabs]; simpa [table,hd] using member
  cases before : g.dev with
  | none => simp [table,before] at oldMember
  | some d =>
    obtain ⟨k,resident,positive⟩ := live d before e (by simpa [table,before] using oldMember) kid owner
    have stored : keyMap f kid = some (KeyCell k) := by
      rw [keys]; simp [keyMap,before,resident]
    cases actual : final.keypairs[kid]? with
    | none => simp [keyMap,hd,actual] at stored
    | some q =>
      simp only [keyMap,hd,Option.bind_some,actual,Option.map_some,Option.some.injEq] at stored
      have eq := congrArg Prod.snd stored
      exact ⟨q,rfl,by simpa [KeyCell,positive] using eq⟩

end Leanux.Proofs.WG.Index.StagingRich
