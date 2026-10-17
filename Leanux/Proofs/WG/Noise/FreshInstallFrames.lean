import Leanux.Proofs.WG.Noise.FreshInstallModel
import Leanux.Proofs.WG.Noise.InitiationTagFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Internal native preservation predicate, separate from projected claims. -/
def FreshTransport (tracked : PeerId) (entry : Option Device) (g : WGWorld) : Prop :=
  freshInstallView tracked g.dev = freshInstallView tracked entry

/-- A real public-key acquisition supplies the extra reference used by a
later rejection. No public reference budget is postulated. -/
def FreshTransportHeld (tracked : PeerId) (entry : Option Device) (pid : PeerId)
    (g : WGWorld) : Prop :=
  FreshTransport tracked entry g ∧
    ∃ d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount

theorem freshInstallView_write (tracked writer : PeerId) (d : Device) (p q : Peer)
    (resident : d.peers[writer]? = some p) (next : q.keypairNext = p.keypairNext) :
    freshInstallView tracked (some {d with peers := d.peers.insert writer q}) =
      freshInstallView tracked (some d) := by
  by_cases same : writer = tracked
  · subst tracked; simp [freshInstallView,resident,next]
  · simp [freshInstallView,Std.TreeMap.getElem?_insert,same]

/-- Variant of Keypairs.Frames.WGTransitions.modifyPeer_spec for the exact cursor
and tracked next slot. Missing writers retain the original Stop. -/
theorem modifyPeer_spec_freshTransport_variant (tracked : PeerId) (entry : Option Device)
    (writer : PeerId) (f : Peer → Peer) (next : ∀ p, (f p).keypairNext = p.keypairNext) :
    Ensures (modifyPeer writer f) (FreshTransport tracked entry)
      (fun _ => FreshTransport tracked entry) := by
  intro g ambient result final after pre run
  change (((do let p ← getPeer writer; setPeer writer (f p)) : WG.M Unit).run g).run ambient = _ at run
  cases device : g.dev with
  | none => simp [getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    cases resident : d.peers[writer]? with
    | none => simp [getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p =>
      simp [getPeer,getDev,device,resident,setPeer,modifyDev] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact (freshInstallView_write tracked writer d p (f p) resident (next p)).trans
        (by simpa [FreshTransport,device] using pre)

/-- The same owned write contract retains its actual held reference. -/
theorem modifyPeer_freshTransportHeld (tracked : PeerId) (entry : Option Device)
    (pid : PeerId) (f : Peer → Peer) (next : ∀ p, (f p).keypairNext = p.keypairNext)
    (count : ∀ p, (f p).refcount = p.refcount) :
    Ensures (modifyPeer pid f) (FreshTransportHeld tracked entry pid)
      (fun _ => FreshTransportHeld tracked entry pid) := by
  intro g ambient result final after pre run
  have preserved := modifyPeer_spec_freshTransport_variant tracked entry pid f next
    g ambient result final after pre.1 run
  obtain ⟨_,d,p,device,resident,held⟩ := pre
  change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
  simp [getPeer,getDev,device,resident,setPeer,modifyDev] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  exact ⟨preserved,_,f p,rfl,by simp,by rw [count]; exact held⟩

/-- Actual lookup effect plus its already checked held-reference contract.
Variant of Keypairs.Frames.WGBase.pubkeyLookup_spec; acquisition uses the
already checked original lookup effect. -/
theorem pubkeyLookup_spec_freshTransport_variant (tracked : PeerId) (entry : Option Device)
    (key : Key) : Ensures (pubkeyLookup key) (FreshTransport tracked entry)
      (fun result g => FreshTransport tracked entry g ∧
        ∀ pid, result = some pid → FreshTransportHeld tracked entry pid g) := by
  intro g ambient result final after pre run
  have acquired := pubkeyLookup_spec_initiationTagMap_variant key g.dev
    g ambient result final after rfl run
  have preserved : FreshTransport tracked entry final := by
    cases device : g.dev with
    | none => simp [pubkeyLookup,getDev,device,invariant,AmbientM.invariant] at run; cases run
    | some d =>
      cases found : d.peerHashtable.find? (·.1 == key) with
      | none =>
        simp [pubkeyLookup,getDev,device,found,peerGetMaybeZero,branch,AmbientM.branch] at run
        rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
      | some pair =>
        obtain ⟨name,pid⟩ := pair
        cases resident : d.peers[pid]? with
        | none =>
          simp [pubkeyLookup,getDev,device,found,peerGetMaybeZero,requireNotPending,getPeer,
            resident,branch,AmbientM.branch,invariant,AmbientM.invariant] at run
          cases run
        | some p =>
          by_cases zero : p.refcount = 0
          · simp [pubkeyLookup,getDev,device,found,peerGetMaybeZero,requireNotPending,getPeer,
              resident,refcountIncNotZero,zero,branch,branchCmp,AmbientM.branch,AmbientM.branchCmp] at run
            rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
          · have nameEq : name = key := by
              have member := List.find?_some found
              simpa using member
            subst name
            have effect := ((ensures_iff _ _ _).mpr (Config.pubkeyLookup_present key pid d p found resident (by omega)))
              g ambient result final after device run
            change freshInstallView tracked final.dev = _
            rw [effect.2]
            exact (freshInstallView_write tracked pid d p {p with refcount := p.refcount+1} resident rfl).trans
              (by simpa [FreshTransport,device] using pre)
  refine ⟨preserved,?_⟩
  intro pid returned
  exact ⟨preserved,(acquired.2 pid returned).2⟩

/-- Reuse the exact retained-put effect. Acquisition ensures this is non-final;
no deletion-capable shared release layer is copied. -/
theorem peerPut_freshTransportHeld (tracked : PeerId) (entry : Option Device) (pid : PeerId) :
    Ensures (peerPut (some pid)) (FreshTransportHeld tracked entry pid)
      (fun _ => FreshTransport tracked entry) := by
  intro g ambient result final after pre run
  obtain ⟨same,d,p,device,resident,held⟩ := pre
  have effect := ((ensures_iff _ _ _).mpr (Config.peerPut_retained pid d p resident held))
    g ambient result final after device run
  change freshInstallView tracked final.dev = _
  rw [effect]
  exact (freshInstallView_write tracked pid d p {p with refcount := p.refcount-1} resident rfl).trans
    (by simpa [FreshTransport,device] using same)

/-- Exact optional observations carry the named initial next/cursor bound. -/
theorem freshNextBound_of_view (tracked : PeerId) (entry after : Campaign2.Snapshot)
    (same : freshInstallView tracked after.wg.device = freshInstallView tracked entry.wg.device)
    (bound : FreshNextBound tracked entry) : FreshNextBound tracked after := by
  intro d peer id device resident next
  have cursor := congrArg Prod.fst same
  have pending := congrArg Prod.snd same
  cases original : entry.wg.device with
  | none => simp [freshInstallView,device,original] at cursor
  | some old =>
    have sameCursor : d.nextKeypairId = old.nextKeypairId := by
      simpa [freshInstallView,device,original] using cursor
    cases found : old.peers[tracked]? with
    | none => simp [freshInstallView,device,resident,original,found] at pending
    | some before =>
      have sameNext : peer.keypairNext = before.keypairNext := by
        simpa [freshInstallView,device,resident,original,found] using pending
      rw [sameCursor]
      exact bound old before id original found (sameNext.symm.trans next)


end Leanux.Proofs.WG.Noise
