import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHolderFrames

/-! Native peer creation contributes one initial reference before publication.
The same occurrence becomes the base holder only after the original initializer
returns; errors keep the original account. No count slack becomes a holder. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits Std.Do
open DurableHolders
variable {holders : DurableHolders} {carriers : RxCredits.Ledger}
  {loans : Reservations} {w v : WGWorld} {a b : Ambient} {d : Device}

/-- Reuse C1's exact original allocation projection. Vacancy is discharged by
ConfiguredIdentity at the enclosing native caller. -/
theorem Upper.creation_core (upper : Upper holders carriers loans w)
    (device : w.dev = some d) (vacant : d.peers[d.nextPeer]? = none) (key : Key) :
    Upper holders carriers (BaseCreation.owner w d :: loans)
      (Peers.creationCoreWorld w d.nextPeer key) := by
  intro owner
  have equation := (pinned_const
    _private.Leanux.Proofs.WG.Queues.BaseCreation.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCreation.core_balance)
    device vacant key owner
  rw [equation]
  by_cases same : owner = BaseCreation.owner w d
  · subst owner
    simp [demand]
    omega
  · rw [ite_eq_right same]
    simpa [demand,List.count_cons,Ne.symm same] using upper owner

theorem Upper.creation_finish (upper : Upper holders carriers (owner :: loans) w)
    (pid : PeerId) (key : Key) (psk : Option Key)
    (run : ((BaseCreation.finish pid key psk).run w).run a = .ok (((),v),b)) :
    Upper (HolderCreation.addBase holders owner) carriers loans v := by
  have fields := BaseCreation.finish_normal pid key psk w v a b run
  have peers : peerView v = peerView w := congrArg (fun s => s.1.1) fields.1
  exact (upper.peer_view peers).publish

/-- Whole native creation returns an upper account for the exact same
allocated owner used by C1's funded result, including ordinary errno arms. -/
theorem Upper.peer_create (upper : Upper holders carriers loans w)
    (configured : ConfiguredIdentity.Inv w) (key : Key) (psk : Option Key)
    (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    match result with
    | .error _ => Upper holders carriers loans v
    | .ok pid => ∃ d, w.dev = some d ∧ pid = d.nextPeer ∧
        Upper (HolderCreation.addBase holders (BaseCreation.owner w d)) carriers loans v := by
  let Q := fun (r : Except Int PeerId) (out : WGWorld) => match r with
    | .error _ => Upper holders carriers loans out
    | .ok pid => ∃ d, w.dev = some d ∧ pid = d.nextPeer ∧
        Upper (HolderCreation.addBase holders (BaseCreation.owner w d)) carriers loans out
  have getter : Hoare getDev (fun u => u = w) (fun d u => u = w ∧ w.dev = some d) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u aa d out bb hu hr
    subst u
    obtain ⟨same,_,device⟩ := DecryptCarrier.getDev_current aa bb hr
    exact ⟨same,by simpa only [same] using device⟩
  have proof : Hoare (peerCreate key psk) (fun u => u = w) Q := by
    rw [BaseCreation.peerCreate_factor]
    apply hoare_bind _ _ getter
    intro d
    let P := fun u => u = w ∧ w.dev = some d
    have ambient {α : Type} (act : AmbientM α) : Preserves P (monadLift act : WG.M α) :=
      hoare_liftAmbient act P
    have failure : Hoare (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId)) P Q := by
      apply hoare_consequence (hoare_pure _ P)
      · exact fun _ h => h
      · intro r u h
        rcases h with ⟨rfl,hu,_⟩
        subst u
        exact upper
    apply hoare_bind _ _ (ambient (AmbientM.branchCmp .peerCreateMaxPeers
      (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE))
    intro maxPeers
    cases maxPeers with
    | true => exact failure
    | false =>
      apply hoare_bind _ _ (ambient (AmbientM.hiddenAlloc .kmemCacheZallocPeer))
      intro allocated
      apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateNoMem !allocated))
      intro noMem
      cases noMem with
      | true => exact failure
      | false =>
        apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateDstCacheFail false))
        intro cacheFailed
        cases cacheFailed with
        | true => exact failure
        | false =>
          have core : Hoare (Peers.peerCreateCore d.nextPeer key) P
              (fun _ u => w.dev = some d ∧ Upper holders carriers (BaseCreation.owner w d :: loans) u) := by
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro u aa x out bb h hr
            rcases h with ⟨rfl,device⟩
            rw [Peers.peerCreateCore_run] at hr
            cases hr
            exact ⟨device,upper.creation_core device (BaseCreation.frontier_vacant configured device) key⟩
          apply hoare_bind _ _ core
          intro _
          have finish : Hoare (BaseCreation.finish d.nextPeer key psk)
              (fun u => w.dev = some d ∧ Upper holders carriers (BaseCreation.owner w d :: loans) u)
              (fun _ u => Q (.ok d.nextPeer) u) := by
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro u aa x out bb h hr
            cases x
            exact ⟨d,h.1,rfl,h.2.creation_finish d.nextPeer key psk hr⟩
          apply hoare_bind _ _ finish
          intro _
          apply hoare_consequence (hoare_pure (Except.ok d.nextPeer : Except Int PeerId) _)
          · exact fun _ h => h
          · intro r u h
            rcases h with ⟨rfl,h⟩
            exact h
  have out := (hoare_iff_run_ambient _ _ _).mp proof w a result v b rfl run
  cases result <;> exact out

/-- The lower and upper proofs are joined using the actual unique entry
Device, so their successful owner and holder list cannot be chosen separately. -/
theorem Account.peer_create (account : Account holders carriers loans w)
    (configured : ConfiguredIdentity.Inv w) (key : Key) (psk : Option Key)
    (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    match result with
    | .error _ => Account holders carriers loans v
    | .ok pid => ∃ d, w.dev = some d ∧ pid = d.nextPeer ∧
        Account (HolderCreation.addBase holders (BaseCreation.owner w d)) carriers loans v := by
  have funded := HolderCreation.peerCreate_funded key psk account.funded account.stable configured a b run
  have upper := account.upper.peer_create configured key psk run
  cases result with
  | error error => exact ⟨funded.1,upper,funded.2⟩
  | ok pid =>
    obtain ⟨d,device,slot,funded,stable⟩ := funded
    obtain ⟨other,otherDevice,_,upper⟩ := upper
    have same := Option.some.inj (device.symm.trans otherDevice)
    subst other
    exact ⟨d,device,slot,funded,upper,stable⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
