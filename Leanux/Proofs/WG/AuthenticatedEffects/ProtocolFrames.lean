import Leanux.Proofs.WG.AuthenticatedEffects.ResponseRefusal

/-! Complete peer protocol records with only the two reference-accounting
fields masked. Index lookup may increment a reference or clear a failed nullable
owner word, but neither action changes any session, endpoint or timer field. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Queues.RxCredits
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def protocolPeer (p : Peer) : Peer := {p with refcount := 0,handshakeEntryPeer := none}
def peerProtocolView (w : WGWorld) := fun pid : PeerId =>
  (w.dev.bind fun d => d.peers[pid]?).map protocolPeer

theorem protocol_insert (w : WGWorld) (d : Device) (pid : PeerId) (old p : Peer)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some old)
    (same : protocolPeer p = protocolPeer old) :
    peerProtocolView {w with dev := some {d with peers := d.peers.insert pid p}} = peerProtocolView w := by
  funext q
  by_cases eq : pid = q
  · subst q; simp [peerProtocolView,hd,hp,same]
  · simp [peerProtocolView,hd,Std.TreeMap.getElem?_insert,eq]

theorem peerGetMaybeZero_protocol (peer : Option PeerId) :
    SameView peerProtocolView (peerGetMaybeZero peer) := by
  apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have borrowed := ((hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec peer (wgStoreView w)) w a result v b rfl run).2
  cases result with
  | none =>
    have same := congrArg WGStoreView.dev borrowed
    change v.dev = w.dev at same
    funext q
    simp only [peerProtocolView,same]
  | some pid =>
    obtain ⟨d,p,hd,hp,_,same⟩ := borrowed
    have changed := congrArg WGStoreView.dev same
    change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} at changed
    change w.dev = some d at hd
    funext q
    simpa only [peerProtocolView,changed] using congrFun (protocol_insert w d pid p
      {p with refcount := p.refcount + 1} hd hp rfl) q

theorem ownerStore_protocol (owner : IndexOwner) (word : Option PeerId) :
    SameView peerProtocolView (owner.setPeerWord word) := by
  apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  cases owner with
  | handshake pid =>
    unfold IndexOwner.setPeerWord at run
    rw [Leanux.Proofs.WG.MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨p,u,c,read,write⟩ := run
    obtain ⟨same,ambient,d,hd,hp⟩ := Leanux.Proofs.WG.Queues.getPeer_normal pid w u p a c read
    subst u
    subst c
    have frame := protocol_insert w d pid p {p with handshakeEntryPeer := word} hd hp rfl
    cases write
    simpa only [hd,Option.map_some] using frame
  | keypair kid =>
    obtain ⟨d,k,hd,_,rfl,_⟩ := Leanux.Proofs.WG.Origins.keypair_word_store kid word w v a b run
    funext q
    simp [peerProtocolView,CounterWindow.store,hd]

theorem indexLookup_protocol (kinds : List IndexKind) (index : Nat) :
    SameView peerProtocolView (indexLookup kinds index) := by
  intro initial
  change Preserves (fun w => peerProtocolView w = initial) _
  have indices {α : Type} (action : IndexM α) :
      Preserves (fun w => peerProtocolView w = initial) (monadLift action : WG.M α) := by
    apply hoare_liftIndex
    intro w d table hi hd
    have same : peerProtocolView {w with dev := some {d with indexTable := table}} = peerProtocolView w := by
      funext q
      simp [peerProtocolView,hd]
    exact same.trans hi
  unfold indexLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (cookie_source_head IndexOwner.peerWord
       exact indexOwner_peerWord_preserves _ (fun w => peerProtocolView w = initial))
    | (cookie_source_head IndexOwner.setPeerWord; exact (ownerStore_protocol _ _).wp (fun v => v = initial))
    | (cookie_source_head peerGetMaybeZero; exact (peerGetMaybeZero_protocol _).wp (fun v => v = initial))
    | (cookie_source_head ForIn.forIn
       apply list_view_spec peerProtocolView (fun v => v = initial)
       intro e state
       change Preserves (fun w => peerProtocolView w = initial) _)
    | (cookie_source_lift IndexM; exact indices _)
    | (cookie_source_lift AmbientM; exact hoare_liftAmbient _ _)
    | cookie_source_step

def RepaySafe (pid : PeerId) (w : WGWorld) : Prop :=
  ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount

theorem loan_repay_safe (w v : WGWorld) (pid : PeerId) (loan : Loan w (some pid) v) :
    RepaySafe pid v := by
  obtain ⟨d,p,hd,hp,positive,peers,_⟩ := loan
  have selected := congrFun (congrArg Prod.snd peers) pid
  simp only [peerView,creditWorld,Option.bind_some,Std.TreeMap.getElem?_insert_self,
    Option.map_some] at selected
  obtain ⟨q,resident,same⟩ := Option.map_eq_some_iff.mp selected
  obtain ⟨dv,hv,hq⟩ := Option.bind_eq_some_iff.mp resident
  have count : q.refcount = p.refcount + 1 := congrArg (fun x => x.2.1) same
  exact ⟨dv,q,hv,hq,by omega⟩

theorem peerPut_protocol (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (safe : RepaySafe pid w)
    (run : ((peerPut (some pid)).run w).run a = .ok (((),v),b)) :
    peerProtocolView v = peerProtocolView w := by
  obtain ⟨d,p,hd,hp,count⟩ := safe
  have positive : 0 < p.refcount := by omega
  have zero : p.refcount ≠ 0 := by omega
  have final : p.refcount ≠ 1 := by omega
  simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,refcountDecAndTest,
    branch,branchCmp,branch_run,branchCmp_run,hd,hp,positive,zero,final,
    StateT.run_bind,StateT.run_pure,StateT.run_monadLift,except_ok_bind,except_pure] at run
  obtain ⟨rfl,_⟩ := run
  exact protocol_insert w d pid p {p with refcount := p.refcount - 1} hd hp rfl

end Leanux.Proofs.WG.AuthenticatedEffects
