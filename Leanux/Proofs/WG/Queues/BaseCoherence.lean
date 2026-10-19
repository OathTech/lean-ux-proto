import Leanux.Proofs.WG.Queues.HolderCreation
import Leanux.Proofs.WG.Queues.HolderSingleRetirement
import Leanux.Proofs.WG.AllowedIps.RoutingAcquire

/-! The live base list is unique and contains every public-key-table target.
This structural invariant does not manufacture reference credit. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

def slots (w : WGWorld) := (w.dev.map Device.peerList).getD []
def rows (w : WGWorld) := (w.dev.map Device.peerHashtable).getD []
def view (w : WGWorld) := (slots w,rows w)
def Inv (w : WGWorld) : Prop := (slots w).Nodup ∧ ∀ row ∈ rows w, row.2 ∈ slots w

theorem transport (hi : Inv w) (same : view v = view w) : Inv v := by
  obtain ⟨list,table⟩ := Prod.mk.inj same
  simpa only [Inv,list,table] using hi

theorem initial (net bare : Bool) : Inv (Runner.initialWG net bare) := by
  cases net <;> cases bare <;> simp [Inv,slots,rows,Runner.initialWG]

theorem holder_unique {h : DurableHolders} (hi : Inv w) (aligned : h.Aligned w) :
    (h.base.map Owner.slot).Nodup := aligned.base ▸ hi.1

private theorem rows_of_configured (same : ConfiguredIdentity.view v = ConfiguredIdentity.view w) : rows v = rows w :=
  by simpa only [rows,ConfiguredIdentity.view,ConfiguredIdentity.state,Option.map_map,Function.comp_def] using
    congrArg (fun s : Option ConfiguredIdentity.State => (s.map ConfiguredIdentity.State.rows).getD []) same

private theorem borrow_view (borrowed : PeerBorrow.Borrowed (wgStoreView w) result (wgStoreView v)) : view v = view w := by
  cases result with
  | none =>
    exact congrArg (fun s : WGStoreView => view {dev := s.dev}) borrowed
  | some pid =>
    obtain ⟨d,p,hd,_,_,out⟩ := borrowed
    have out := congrArg WGStoreView.dev out
    change w.dev=some d at hd
    change v.dev=some _ at out
    simp [view,slots,rows,hd,out]

theorem pubkeyLookup_view (key : Key) : SameView view (pubkeyLookup key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact borrow_view ((hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.pubkeyLookup_borrowed_spec key (wgStoreView w)) w a result v b rfl run)

/-- A successful actual lookup selects an existing base occurrence; its
reference acquisition and configured identity come from the same run. -/
theorem lookup_selected (key : Key) (hi : Inv w) (configured : ConfiguredIdentity.Inv w)
    {h : DurableHolders} (aligned : h.Aligned w) (a b : Ambient)
    (run : ((pubkeyLookup key).run w).run a = .ok ((some pid,v),b)) :
    Inv v ∧ (h.base.map Owner.slot).Nodup ∧ pid ∈ h.base.map Owner.slot := by
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (pubkeyLookup_view key) w a (some pid) v b run
  obtain ⟨_,d,p,hd,_,row,_⟩ := ConfiguredIdentity.pubkeyLookup_identity key w v pid a b configured run
  refine ⟨transport hi same,holder_unique hi aligned,?_⟩
  rw [aligned.base]
  exact hi.2 (key,pid) (by simpa [rows,hd] using row)

private theorem initializer_view (pid : PeerId) (key : Key) (psk : Option Key)
    (w v : WGWorld) (a b : Ambient)
    (run : ((BaseCreation.finish pid key psk).run w).run a = .ok (((),v),b)) :
    v.dev.map (fun (d : Device) => (d.peerList,d.peerHashtable)) =
      (w.dev.map (fun (d : Device) => (d.peerList,d.peerHashtable))).map
        (fun s => (s.1 ++ [pid],(key,pid)::s.2)) := by
  unfold BaseCreation.finish at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨x,u,au,first,rest⟩ := run; cases x
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨x,j,aj,second,rest⟩ := rest; cases x
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨x,k,ak,third,last⟩ := rest; cases x
  have f1 := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderCreation.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderCreation.dstCacheReset_frame) pid w)
    w a () u au (Frame.refl w) first
  have f2 := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderCreation.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderCreation.handshakeInit_frame) pid psk u)
    u au () j aj (Frame.refl u) second
  have f3 := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderCreation.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderCreation.resetLast_frame) pid j)
    j aj () k ak (Frame.refl j) third
  have c1 := (ProjectedAction.iff_run_ambient _ _ _).mp (ConfiguredIdentity.cacheReset pid) w a () u au first
  have c2 := ConfiguredIdentity.handshakeInit_effect pid psk u j au aj second
  have c3 := (ProjectedAction.iff_run_ambient _ _ _).mp (ConfiguredIdentity.resetHandshake pid) j aj () k ak third
  have list := congrArg Prod.fst (f1.trans (f2.trans f3)).passive
  have table : rows k = rows w := by
    have mid : rows j = rows u := by
      have q := congrArg (fun s : Option ConfiguredIdentity.State => (s.map ConfiguredIdentity.State.rows).getD []) c2
      simpa [rows,ConfiguredIdentity.view,ConfiguredIdentity.state,ConfiguredIdentity.State.setWord,Option.map_map,Function.comp_def] using q
    exact (rows_of_configured c3).trans (mid.trans (rows_of_configured c1))
  have c1p : u.dev.isSome = w.dev.isSome := by
    simpa [ConfiguredIdentity.view] using congrArg Option.isSome c1
  have c2p : j.dev.isSome = u.dev.isSome := by
    simpa [ConfiguredIdentity.view] using congrArg Option.isSome c2
  have c3p : k.dev.isSome = j.dev.isSome := by
    simpa [ConfiguredIdentity.view] using congrArg Option.isSome c3
  have present := c3p.trans (c2p.trans c1p)
  cases last
  cases hk : k.dev <;> cases hw : w.dev
  all_goals simp only [hk,hw,Option.isSome_none,Option.isSome_some] at present
  all_goals try contradiction
  · simp [hk]
  · simp only [passiveView,hk,hw,Option.map_some,Option.getD_some] at list
    simp only [rows,hk,hw,Option.map_some,Option.getD_some] at table
    simp [hk,list,table]

/-- The original creation's only base/table change is its final publication.
Refused creations keep both fields, including their actual decision records. -/
theorem creation_view (key : Key) (psk : Option Key) (w v : WGWorld) (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a=.ok ((result,v),b)) :
    match result with
    | .error _ => view v=view w
    | .ok pid => ∃ d, w.dev=some d ∧ pid=d.nextPeer ∧
        v.dev.map (fun (d : Device) => (d.peerList,d.peerHashtable)) =
          some (d.peerList ++ [pid],(key,pid)::d.peerHashtable) := by
  let Q := fun (result : Except Int PeerId) (v : WGWorld) => match result with
    | .error _ => view v=view w
    | .ok pid => ∃ d, w.dev=some d ∧ pid=d.nextPeer ∧
        v.dev.map (fun (d : Device) => (d.peerList,d.peerHashtable)) =
          some (d.peerList ++ [pid],(key,pid)::d.peerHashtable)
  have getter : Hoare getDev (fun u => u=w) (fun d u => u=w ∧ w.dev=some d) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u aa d out bb eq hr
    subst u
    obtain ⟨rfl,rfl,hd⟩ := DecryptCarrier.getDev_current aa bb hr
    exact ⟨rfl,hd⟩
  have proof : Hoare (peerCreate key psk) (fun u => u=w) Q := by
    rw [BaseCreation.peerCreate_factor]
    apply hoare_bind _ _ getter
    intro d
    let P := fun u => u=w ∧ w.dev=some d
    have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
      hoare_liftAmbient action P
    have failure : Hoare (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId)) P Q := by
      apply hoare_consequence (hoare_pure _ P)
      · exact fun _ h => h
      · intro r u h
        obtain ⟨rfl,rfl,_⟩ := h
        rfl
    have success : Hoare (do
      Peers.peerCreateCore d.nextPeer key
      BaseCreation.finish d.nextPeer key psk
      pure (.ok d.nextPeer)) P Q := by
      apply hoare_bind _ _ (show Hoare (Peers.peerCreateCore d.nextPeer key) P
        (fun _ u => w.dev=some d ∧ u.dev.map (fun (d : Device) => (d.peerList,d.peerHashtable)) = some (d.peerList,d.peerHashtable)) from ?_)
      · intro _
        apply hoare_bind _ _ (show Hoare (BaseCreation.finish d.nextPeer key psk)
          (fun u => w.dev=some d ∧ u.dev.map (fun (d : Device) => (d.peerList,d.peerHashtable)) = some (d.peerList,d.peerHashtable))
          (fun _ u => Q (.ok d.nextPeer) u) from ?_)
        · intro _
          apply hoare_consequence (hoare_pure _ _)
          · exact fun _ h => h
          · intro r u h; obtain ⟨rfl,h⟩ := h; exact h
        · apply (hoare_iff_run_ambient _ _ _).mpr
          intro u aa x out bb h hr
          cases x
          refine ⟨d,h.1,rfl,?_⟩
          simpa only [h.2,Option.map_some] using initializer_view d.nextPeer key psk u out aa bb hr
      · apply (hoare_iff_run_ambient _ _ _).mpr
        intro u aa x out bb h hr
        obtain ⟨rfl,hd⟩ := h
        rw [Peers.peerCreateCore_run] at hr
        cases hr
        exact ⟨hd,by simp [Peers.creationCoreWorld,hd]⟩
    apply hoare_bind _ _ (ambient (AmbientM.branchCmp .peerCreateMaxPeers
      (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE))
    intro over
    cases over with
    | true => exact failure
    | false =>
      apply hoare_bind _ _ (ambient (AmbientM.hiddenAlloc .kmemCacheZallocPeer))
      intro allocated
      apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateNoMem !allocated))
      intro failed
      cases failed with
      | true => exact failure
      | false =>
        apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateDstCacheFail false))
        intro failed
        cases failed with
        | true => exact failure
        | false => exact success
  have out := (hoare_iff_run_ambient _ _ _).mp proof w a result v b rfl run
  cases result <;> exact out

/-- Funding plus frontier vacancy rules out a pre-existing base occurrence.
This does not infer credit from structural list membership. -/
theorem frontier_fresh {h : DurableHolders} (funded : h.Funded cs loans w)
    (configured : ConfiguredIdentity.Inv w) (hd : w.dev=some d) : d.nextPeer ∉ slots w := by
  intro member
  change d.nextPeer ∈ (w.dev.map Device.peerList).getD [] at member
  rw [←funded.aligned.base] at member
  obtain ⟨o,inside,slot⟩ := List.mem_map.mp member
  have held : o ∈ h.owners := by simp only [owners,List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl inside))))
  obtain ⟨p,res⟩ := funded.resident held
  have vacant := BaseCreation.frontier_vacant configured hd
  simp [resident,hd,slot,vacant] at res

/-- Actual creation preserves structural coherence from source-funded entry.
The original errno branch has no structural change. -/
theorem creation_preserves (key : Key) (psk : Option Key) {h : DurableHolders}
    (hi : Inv w) (funded : h.Funded cs loans w) (configured : ConfiguredIdentity.Inv w)
    (a b : Ambient) (run : ((peerCreate key psk).run w).run a=.ok ((result,v),b)) : Inv v := by
  have effect := creation_view key psk w v a b run
  cases result with
  | error e => exact transport hi effect
  | ok pid =>
    obtain ⟨d,hd,rfl,out⟩ := effect
    have unique : d.peerList.Nodup := by simpa [slots,hd] using hi.1
    have fresh : d.nextPeer ∉ d.peerList := by simpa [slots,hd] using frontier_fresh funded configured hd
    cases hv : v.dev with
    | none => simp [hv] at out
    | some after =>
      simp only [hv,Option.map_some,Option.some.injEq,Prod.mk.injEq] at out
      constructor
      · simp only [slots,hv,Option.map_some,Option.getD_some,out.1]
        apply List.pairwise_append.mpr
        refine ⟨unique,by simp,?_⟩
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst y
        intro eq
        exact fresh (eq ▸ hx)
      · intro row member
        simp only [rows,hv,Option.map_some,Option.getD_some,out.2,List.mem_cons] at member
        simp only [slots,hv,Option.map_some,Option.getD_some,out.1,List.mem_append,List.mem_singleton]
        rcases member with same | member
        · exact Or.inr (congrArg Prod.snd same)
        · exact Or.inl (by simpa [slots,hd] using hi.2 row (by simpa [rows,hd] using member))

private theorem makeDead_configured (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((peerMakeDead pid).run w).run a=.ok (((),v),b)) :
    ConfiguredIdentity.view v=(ConfiguredIdentity.view w).map (fun s => s.kill pid) := by
  let P := fun u => ConfiguredIdentity.view u=ConfiguredIdentity.view w
  let Q := fun u => ConfiguredIdentity.view u=(ConfiguredIdentity.view w).map (fun s => s.kill pid)
  have factor : peerMakeDead pid=(do
      modifyDev fun d=>{d with peerList:=d.peerList.filter (·!=pid)}
      removeByPeer pid
      _ ← branch .pubkeyRemoveHashed ((← getDev).peerHashtable.any (·.2 == pid))
      ConfiguredIdentity.killRows pid) := rfl
  have rule : Hoare (peerMakeDead pid) P (fun _ => Q) := by
    rw [factor]
    apply hoare_bind _ _ (ConfiguredIdentity.modifyDev_spec (· = ConfiguredIdentity.view w)
      (fun d => {d with peerList:=d.peerList.filter (·!=pid)}) (fun _ => rfl))
    intro _
    apply hoare_bind _ _ ((ConfiguredIdentity.removeByPeer_view pid).wp (· = ConfiguredIdentity.view w))
    intro _
    apply hoare_bind _ _ (show Preserves P getDev from
      (ConfiguredIdentity.sameWG getDev_sameWGStore).wp (· = ConfiguredIdentity.view w))
    intro d
    apply hoare_bind _ _ (hoare_liftAmbient
      (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid))) P)
    intro _
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u aa x out bb hi hr
    cases x
    change ConfiguredIdentity.view u=ConfiguredIdentity.view w at hi
    simpa only [Q,hi] using ConfiguredIdentity.killRows_view pid u out aa bb hr
  exact (hoare_iff_run_ambient _ _ _).mp rule w a () v b rfl run

/-- The actual detach removes the same target from both structures. -/
theorem makeDead_preserves (pid : PeerId) (hi : Inv w) (a b : Ambient)
    (run : ((peerMakeDead pid).run w).run a=.ok (((),v),b)) : Inv v := by
  have list := congrArg (fun s : Option (List PeerId) => s.getD [])
    (BaseRemoval.peerMakeDead_normal pid w v a b run).2
  have table := congrArg (fun s : Option ConfiguredIdentity.State => (s.map ConfiguredIdentity.State.rows).getD [])
    (makeDead_configured pid w v a b run)
  have lists : slots v=(slots w).filter (· != pid) := by
    cases hd : w.dev <;> simpa [slots,hd] using list
  have tables : rows v=(rows w).filter (·.2 != pid) := by
    cases hd : w.dev <;>
      simpa [rows,ConfiguredIdentity.view,ConfiguredIdentity.state,ConfiguredIdentity.State.kill,
        Option.map_map,Function.comp_def,hd] using table
  constructor
  · rw [lists]
    exact hi.1.filter _
  · intro row member
    rw [tables] at member
    rw [lists]
    obtain ⟨member,keep⟩ := List.mem_filter.mp member
    exact List.mem_filter.mpr ⟨hi.2 row member,keep⟩

/-- Single-peer removal's list hypotheses follow from this structural entry
invariant and its selected live-list target. The actual drains remain. -/
theorem remove_funded (pid : PeerId) {h : DurableHolders}
    (hi : Inv w) (funded : h.Funded cs loans w) (stable : StableRx cs w)
    (selected : pid ∈ slots w) (a b : Ambient)
    (run : ((peerRemove (some pid)).run w).run a=.ok (((),v),b)) :
    DuringWork (h.withoutBase (BaseRemoval.live h.base pid)) cs loans v :=
  peerRemove_some_funded pid funded stable (holder_unique hi funded.aligned)
    (funded.aligned.base ▸ selected) a b run

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
