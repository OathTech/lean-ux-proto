import Leanux.Proofs.WG.AuthenticatedEffects.ResponseProtocol

/-! Full peer records across an actual successful index acquisition. The
projection is pointwise, so rewriting an unchanged owner word does not require
equality of balanced-tree representations. Failed zero-count acquisitions are
separate: this file does not silently assume their owner words are unchanged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Queues.RxCredits
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def residents (w : WGWorld) (pid : PeerId) : Option Peer :=
  w.dev.bind fun d => d.peers[pid]?

def Loan (before : WGWorld) (pid : PeerId) (after : WGWorld) : Prop :=
  ∃ p, residents before pid = some p ∧ 0 < p.refcount ∧
    ∀ q, residents after q = if q = pid then some {p with refcount := p.refcount + 1}
      else residents before q

theorem unchanged_owner_store (owner : IndexOwner) (word : Option PeerId)
    (w v : WGWorld) (a b : Ambient)
    (same : Affiliation.wordAt w owner = some word)
    (run : ((owner.setPeerWord word).run w).run a = .ok (((),v),b)) :
    residents v = residents w := by
  cases owner with
  | handshake pid =>
    unfold IndexOwner.setPeerWord at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨p,u,c,read,write⟩ := run
    obtain ⟨rfl,rfl,d,hd,hp⟩ := Queues.getPeer_normal pid w u p a c read
    have word : p.handshakeEntryPeer = word := by
      simpa [Affiliation.wordAt,Affiliation.view,Affiliation.state,Affiliation.State.word,
        Affiliation.peerCell,hd,hp] using same
    cases write
    funext q
    by_cases equal : pid = q
    · subst q
      simp [residents,hd,hp,←word]
    · simp [residents,hd,Std.TreeMap.getElem?_insert,equal]
  | keypair kid =>
    obtain ⟨d,k,hd,_,rfl,_⟩ := Origins.keypair_word_store kid word w v a b run
    funext q
    simp [residents,CounterWindow.store,hd]

theorem acquire (owner : IndexOwner) (w v : WGWorld) (pid : PeerId) (a b : Ambient)
    (run : ((Affiliation.acquireOwner owner).run w).run a = .ok ((some pid,v),b)) :
    Loan w pid v := by
  obtain ⟨word,u,q,c,d,read,borrow,write⟩ := Affiliation.acquireOwner_acquisition owner w v (some pid) a b run
  have world : u = w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerWord_preserves owner (fun z => z = w))
    w a word u c rfl read
  subst u
  have readWord := ((hoare_iff_run_ambient _ _ _).mp
    (Affiliation.peerWord_spec owner (fun _ => True)) w a word w c True.intro read).2
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec word (wgStoreView w)) w c (some pid) q d rfl borrow
  have sameWord : word = some pid := borrowed.1.resolve_left (by simp) |>.symm
  have affiliation := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (Affiliation.peerGetMaybeZero_view word) w c (some pid) q d borrow
  have currentWord : Affiliation.wordAt q owner = some (some pid) := by
    simpa only [Affiliation.wordAt,affiliation,sameWord] using readWord
  have frame := unchanged_owner_store owner (some pid) q v d b currentWord write
  obtain ⟨device,p,hd,hp,positive,store⟩ := borrowed.2
  have hq := congrArg WGStoreView.dev store
  change q.dev = some {device with peers := device.peers.insert pid {p with refcount := p.refcount + 1}} at hq
  change w.dev = some device at hd
  refine ⟨p,by simp [residents,hd,hp],positive,?_⟩
  intro id
  rw [congrFun frame]
  by_cases equal : id = pid
  · subst id; simp [residents,hq]
  · simp [residents,hq,hd,Std.TreeMap.getElem?_insert,equal,Ne.symm equal]

end Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
