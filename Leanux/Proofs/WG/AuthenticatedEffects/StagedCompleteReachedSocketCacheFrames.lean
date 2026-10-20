import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketCacheSource

/-! Each cached write is funded by the peer returned at its actual read.
The intervening clock input preserves that resident peer, including on the
native write side of the lifetime receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketCache
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Prepare.Points

theorem update_framed (pid : PeerId) (f : Peer → Peer)
    (same : ∀p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue)
    (h : List LifetimeEvent) : Framed (update pid f) w a h := by
  refine ⟨True.intro,?_⟩
  intro p v b middle read
  have native : (getPeer pid).run w a=.ok ((p,v),b) :=
    (getPeerMixed_erases pid w a h).symm.trans (congrArg Prod.fst read)
  obtain ⟨rfl,rfl,d,device,resident⟩:=read_peer_resident native
  exact ⟨d,p,device,resident,same p⟩

theorem miss_framed (pid : PeerId) (p : Peer) (d : Device)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) (h : List LifetimeEvent) :
    Framed (missShape pid p) w a h := by
  refine ⟨True.intro,?_⟩
  intro ts v b middle readClock
  have same : v=w := by
    have frame : SameView (fun w : WGWorld=>w) (monadLift (AmbientM.hiddenJiffies .dstCacheRefreshTs) : WG.M UInt64) :=
      fun initial=>hoare_liftAmbient _ (fun w=>w=initial)
    rw [runWGPrefix_lift] at readClock
    exact (ProjectedAction.iff_run_ambient _ _ _).mp frame _ _ _ _ _ (congrArg Prod.fst readClock)
  subst v
  exact ⟨⟨d,p,device,resident,rfl,rfl,rfl⟩,fun _ _ _ _ _=>True.intro⟩

theorem afterRead_framed (pid : PeerId) (gen : Nat) (p : Peer) (d : Device)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) (h : List LifetimeEvent) :
    Framed (afterReadShape pid gen p) w a h := by
  unfold afterReadShape
  dsimp only
  prepare_framed_uncast
  apply optionShape_framed
  · exact miss_framed pid p d device resident h
  intro slot
  exact boolShape_framed _ _ _ h True.intro (miss_framed pid p d device resident h)

theorem get_framed (pid : PeerId) (gen : Nat) (h : List LifetimeEvent) :
    Framed (getShape pid gen) w a h := by
  unfold getShape
  refine ⟨True.intro,?_⟩
  intro ambient v b middle readAmbient
  refine ⟨True.intro,?_⟩
  intro world u c last readWorld
  apply boolShape_framed
  · exact True.intro
  · refine ⟨True.intro,?_⟩
    intro p q aq hq read
    have native : (getPeer pid).run u c=.ok ((p,q),aq) :=
      (getPeerMixed_erases pid u c last).symm.trans (congrArg Prod.fst read)
    obtain ⟨rfl,rfl,d,device,resident⟩:=read_peer_resident native
    exact afterRead_framed pid gen p d device resident hq

theorem set_framed (pid : PeerId) (src gen dev : Nat) (h : List LifetimeEvent) :
    Framed (setShape pid src gen dev) w a h :=
  update_framed pid (fun p=>{p with dstCache:={p.dstCache with slot:=some {src,gen,dev}}}) (fun _=>⟨rfl,rfl,rfl⟩) h

theorem reset_framed (pid : PeerId) (h : List LifetimeEvent) : Framed (resetShape pid) w a h := by
  unfold resetShape
  refine ⟨True.intro,?_⟩
  intro ambient v b middle readAmbient
  refine ⟨True.intro,?_⟩
  intro world u c last readWorld
  apply boolShape_framed
  · exact True.intro
  refine ⟨True.intro,?_⟩
  intro ts q aq hq readClock
  exact update_framed pid (fun p=>{p with dstCache:={p.dstCache with resetTs:=ts}}) (fun _=>⟨rfl,rfl,rfl⟩) hq

theorem clear4_framed (cache : Option PeerId) (h : List LifetimeEvent) : Framed (clear4Shape cache) w a h := by
  cases cache with
  | none=>exact True.intro
  | some pid=>
      exact update_framed pid (fun p=>{p with endpoint:=p.endpoint.map fun e=>{e with src:=0,srcIf:=0}})
        (fun _=>⟨rfl,rfl,rfl⟩) h

theorem clear6_framed (cache : Option PeerId) (h : List LifetimeEvent) : Framed (clear6Shape cache) w a h := by
  cases cache with
  | none=>exact True.intro
  | some pid=>
      exact update_framed pid (fun p=>{p with endpoint:=p.endpoint.map fun e=>{e with src:=0}})
        (fun _=>⟨rfl,rfl,rfl⟩) h

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketCache
