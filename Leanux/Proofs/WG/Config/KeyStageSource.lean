import Leanux.Proofs.WG.Config.KeyStageModel
import Leanux.Proofs.WG.Config.QueuedRemoveSource
import Leanux.Proofs.WG.Config.ConfiguredDeviceSource
import Leanux.Proofs.WG.Config.CollisionRemovalModel
import Leanux.Proofs.WG.Config.RequestOrderReceiptBridge

/-! Exact source cuts for private-key configuration, retaining real lookup
funding, queued removal and the original saved-peer installation loop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.KeyStage
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration
theorem lookup_effect (cs : Ledger) (loans : Reservations) (pub : Key) (before : Device)
    (g v : WGWorld) (a b : Ambient)
    (pre : Entry cs loans g) (device : g.dev=some before)
    (run : ((do
      let peer ← pubkeyLookup pub
      if ← branch .setDevOldPeer peer.isSome then
        peerPut peer
        peerRemove peer : WG.M Unit).run g).run a=.ok (((),v),b)) :
    Entry cs loans v ∧ ∃ after,v.dev=some after ∧ LookupEffect before pub after := by
  have post : Entry cs loans v := ⟨
    Index.ConfigurationIndex.keyConflict cs loans pub g a () v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp (conflict_ready pub) g a () v b pre.2 run⟩
  refine ⟨post,?_⟩
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨selected,u,c,looked,tail⟩ := run
  cases found : before.peerHashtable.find? (·.1 == pub) with
  | none =>
    obtain ⟨selectedEq,stateEq⟩ := (ensures_iff _ _ _).mpr
      (pubkeyLookup_absent pub g before device found) g a selected u c rfl looked
    subst selected
    subst u
    change Except.ok (((),g),CounterWindow.record c .setDevOldPeer false)=.ok (((),v),b) at tail
    cases tail
    exact ⟨before,device,.absent found⟩
  | some row =>
    obtain ⟨key,pid⟩ := row
    have keyeq : key=pub := by
      have yes := List.find?_some found
      simpa only [beq_iff_eq] using yes
    subst key
    obtain ⟨p,resident,positive⟩ := QueuedRemove.lookup_target cs loans pub pid before g pre device found
    obtain ⟨rfl,acquired⟩ := (ensures_iff _ _ _).mpr
      (pubkeyLookup_present pub pid before p found resident positive) g a selected u c device looked
    change ((peerPut (some pid) >>= fun _=>peerRemove (some pid)).run u).run
      (CounterWindow.record c .setDevOldPeer true)=.ok (((),v),b) at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,z,next,paid,removed⟩ := tail
    cases ignored
    have restored := (ensures_iff _ _ _).mpr
      (peerPut_retained pid (withPeer before pid {p with refcount:=p.refcount+1})
        {p with refcount:=p.refcount+1} (by simp [withPeer]) (by change 1<p.refcount+1; omega))
      u _ () z next acquired paid
    have point : z.dev=some (collisionLookupDevice before pid p) := by
      simpa only [collisionLookupDevice,Nat.add_sub_cancel] using restored
    obtain ⟨after,present,_⟩ := post.2
    have cut := QueuedRemove.remove_base pid z v next b removed
    have members : after.peerList=before.peerList.filter (· != pid) := by
      simpa only [BaseCoherence.slots,point,present,Option.map_some,Option.getD_some,
        collisionLookupDevice,withPeer] using cut.1
    have rows : after.peerHashtable=before.peerHashtable.filter (·.2 != pid) := by
      simpa only [BaseCoherence.rows,point,present,Option.map_some,Option.getD_some,
        collisionLookupDevice,withPeer] using cut.2
    exact ⟨after,present,.removed pid p after found resident positive
      (QueuedRemove.effect_of_entry cs loans before after pid v present post members rows)⟩

theorem stage_factor (attrs : DeviceAttrs) :
    RequestOrder.keyStage attrs = (do
      if ← WG.andM (branch .setDevHasPrivateKey attrs.privateKey.isSome)
          (branch .setDevPrivateKeyLen true) then
        let some key := attrs.privateKey | invariant "unreachable"
        if !(← branch .setDevKeyUnchanged ((← getDev).staticIdentity.staticPrivate == key)) then
          keyCollisionSource key
          keyInstallSource key
      pure 0 : WG.M Int) := by
  have bind_cond {α β : Type} (c : Prop) [Decidable c]
      (a b : WG.M α) (f : α → WG.M β) :
      (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
    split <;> rfl
  have map_cond (yes : Bool) (action : WG.M Unit) :
      ((fun (_ : Unit)=>ForInStep.yield PUnit.unit) <$> (if yes then action else pure ())) =
        (if yes then (fun (_ : Unit)=>ForInStep.yield PUnit.unit) <$> action
        else pure (ForInStep.yield PUnit.unit)) := by
    cases yes <;> simp
  simp [RequestOrder.keyStage,deviceKeyWith,keyCollisionSource,keyInstallSource,
    keyPeerLoopSource,keyPeerSource,bind_assoc,bind_cond,map_cond]
  congr 1
  funext has
  cases has <;> simp
  cases h : attrs.privateKey with
  | none => simp
  | some key =>
    simp only
    congr 1
    funext d
    congr 1
    funext unchanged
    cases unchanged <;> simp
    congr 1
    funext pair
    obtain ⟨pub,ok⟩ := pair
    congr 1
    funext generated
    cases generated <;> simp
    cases pub <;> simp [bind_assoc,bind_cond]

theorem generated_effect (cs : Ledger) (loans : Reservations) (key : Key) (before : Device)
    (g v : WGWorld) (a b : Ambient)
    (pre : Entry cs loans g) (device : g.dev=some before)
    (run : ((keyCollisionSource key).run g).run a=.ok (((),v),b)) :
    Entry cs loans v ∧ ∃ after,v.dev=some after ∧ GeneratedEffect before key after := by
  unfold keyCollisionSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨pair,u,c,generated,tail⟩ := run
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (generatePublic_sameWGWorld key) g a pair u c generated
  change u=g at frame
  subst u
  obtain ⟨value,out,after,returned,gen⟩ := generatePublic_return key before g a device
  rw [generated] at returned
  cases returned
  rcases gen with ⟨rfl,_⟩
  cases ok : (publicResult key).2 with
  | false =>
    simp only [ok] at tail
    change Except.ok (((),g),CounterWindow.record c .setDevGenPublic false)=.ok (((),v),b) at tail
    cases tail
    exact ⟨pre,before,device,Or.inl ⟨ok,rfl⟩⟩
  | true =>
    obtain ⟨pub,present⟩ := publicResult_valid key ok
    have full : publicResult key=(some pub,true) := Prod.ext present ok
    simp only [full] at tail
    change ((do
      let peer ← pubkeyLookup pub
      if ← branch .setDevOldPeer peer.isSome then
        peerPut peer
        peerRemove peer : WG.M Unit).run g).run
      (CounterWindow.record c .setDevGenPublic true)=.ok (((),v),b) at tail
    obtain ⟨entry,after,dev,effect⟩ := lookup_effect cs loans pub before g v _ b pre device tail
    exact ⟨entry,after,dev,Or.inr ⟨pub,full,effect⟩⟩

theorem install_effect (before : Device) (key : Key)
    (g v : WGWorld) (a b : Ambient) (device : g.dev=some before)
    (run : ((keyInstallSource key).run g).run a=.ok (((),v),b)) :
    ∃ after observations,v.dev=some after ∧
      ObservedKeyPeerRun (requestsStagedSend before key)
        (installedDevice before key) before.peerList observations after := by
  have erased := observedKeyInstallSource_erase key before g a device
  change (((observedKeyInstallSource key).run g).run a >>= _) = _ at erased
  rw [run] at erased
  cases observed : ((observedKeyInstallSource key).run g).run a with
  | error stop => rw [observed] at erased; cases erased
  | ok out =>
    obtain ⟨⟨observations,current⟩,after⟩ := out
    rw [observed] at erased
    cases erased
    obtain ⟨done,dev,effect⟩ := keyInstall_complete before key
      g a observations v b device observed
    exact ⟨done,observations,dev,effect⟩


theorem install_factor (key : Key) : keyInstallSource key =
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish
  simp only [keyInstallSource,keyPeerLoopSource,keyPeerSource,bind_assoc,TxDisposition.bind_ite,pure_bind]

theorem install_entry (cs : Ledger) (loans : Reservations) (key : Key) :
    Preserves (Entry cs loans) (keyInstallSource key) := by
  rw [install_factor]
  exact Index.ConfigurationKeyRules.keyFinish _ (key_contracts cs loans) key

theorem stage_effect (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (before : Device) :
    Ensures (RequestOrder.keyStage attrs) (fun g=>Entry cs loans g ∧ g.dev=some before)
      (fun ret g=>ret=0 ∧ Entry cs loans g ∧ ∃ after,g.dev=some after ∧ Effect attrs before after) := by
  intro g a result v b pre run
  rw [stage_factor] at run
  cases input : attrs.privateKey with
  | none =>
    simp only [input,Option.isSome_none,WG.andM,branch,AmbientM.branch,StateT.run] at run
    cases run
    exact ⟨rfl,pre.1,before,pre.2,.absent input⟩
  | some key =>
    by_cases same : before.staticIdentity.staticPrivate=key
    · simp [input,WG.andM,branch,AmbientM.branch,getDev,pre.2,same] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact ⟨rfl,pre.1,before,pre.2,.unchanged key input same⟩
    · have different : (before.staticIdentity.staticPrivate == key)=false := by
        simpa only [beq_eq_false_iff_ne] using same
      let start := CounterWindow.record
        (CounterWindow.record (CounterWindow.record a .setDevHasPrivateKey true)
          .setDevPrivateKeyLen true) .setDevKeyUnchanged false
      have cut : ((RequestOrder.keyStage attrs).run g).run a =
          ((do keyCollisionSource key; keyInstallSource key; pure (0 : Int) : WG.M Int).run g).run start := by
        rw [stage_factor]
        simp [input,WG.andM,branch,AmbientM.branch,getDev,pre.2,same,different,start,CounterWindow.record]
      rw [←stage_factor] at run
      rw [cut,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨ignored,u,c,generated,tail⟩ := run
      cases ignored
      obtain ⟨middle,baseline,device,collision⟩ :=
        generated_effect cs loans key before g u start c pre.1 pre.2 generated
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨ignored,z,next,installed,done⟩ := tail
      cases ignored
      change Except.ok ((0,z),next)=.ok ((result,v),b) at done
      cases done
      have account := (hoare_iff_run_ambient _ _ _).mp
        (install_entry cs loans key) u c () v b middle installed
      obtain ⟨after,observations,present,effect⟩ := install_effect baseline key u v c b device installed
      exact ⟨rfl,account,after,present,.changed key input same baseline after collision observations effect⟩


end Leanux.Proofs.WG.Config.KeyStage
