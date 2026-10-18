import Leanux.Proofs.WG.Queues.BaseCreation
import Leanux.Proofs.WG.Queues.HolderWorkFrames

/-! The real creation path funds its new base occurrence before publication.
Other complete holders stay charged across initialization. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderCreation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders
variable {holders : DurableHolders} {cs : Ledger} {loans : Reservations}
  {w v : WGWorld} {d : Device} {pid : PeerId}

def addBase (h : DurableHolders) (o : Owner) : DurableHolders :=
  {h with base := h.base ++ [o]}

theorem addBase_owners (h : DurableHolders) (o : Owner) :
    (addBase h o).owners.Perm (o :: h.owners) := by
  apply List.perm_iff_count.mpr
  intro q
  simp [addBase,owners,List.count_append,List.count_cons]
  omega

theorem vacant_items (hi : holders.Funded cs loans w) (hd : w.dev = some d)
    (empty : d.peers[pid]? = none) : holders.items pid = [] := by
  unfold items
  suffices h : (holders.tx.filter fun e => e.owner.slot == pid) = [] by rw [h]; rfl
  apply List.filter_eq_nil_iff.mpr
  intro e member selected
  have own : e.owner ∈ holders.owners := by
    simp only [owners,List.mem_append,List.mem_map]
    exact Or.inl (Or.inl (Or.inr ⟨e,member,rfl⟩))
  obtain ⟨p,res⟩ := hi.resident own
  have slot : e.owner.slot = pid := by simpa only [beq_iff_eq] using selected
  simp [resident,hd,slot,empty] at res

theorem core_aligned (hi : holders.Funded cs loans w) (hd : w.dev = some d)
    (empty : d.peers[d.nextPeer]? = none) (key : Key) :
    holders.Aligned (Peers.creationCoreWorld w d.nextPeer key) := by
  refine ⟨?_,?_,?_,?_,hi.aligned.cursor7,hi.aligned.cursor8⟩
  · simpa [Peers.creationCoreWorld,hd] using hi.aligned.base
  · intro out found
    have same : out = {d with nextPeer := d.nextPeer+1, peers := d.peers.insert d.nextPeer (Peers.createdPeer key (w.peerCounter+1))} := by
      simpa [Peers.creationCoreWorld,hd] using found.symm
    subst out
    exact hi.aligned.send d hd
  · simpa [Peers.creationCoreWorld,hd] using hi.aligned.clear
  · intro pid batches found
    by_cases same : d.nextPeer = pid
    · subst pid
      have nil : batches = [] := by
        simpa [handoffTxView,Peers.creationCoreWorld,hd,Peers.createdPeer,PrevQueue.all] using found.symm
      rw [nil,vacant_items hi hd empty]
    · apply hi.aligned.tx pid batches
      simpa [handoffTxView,Peers.creationCoreWorld,hd,Std.TreeMap.getElem?_insert,same] using found

private theorem dstCacheReset_frame (pid : PeerId) (initial) :
    Preserves (Frame initial) (dstCacheReset pid) := by
  unfold dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' holder_work_step initial

private theorem resetLast_frame (pid : PeerId) (initial) :
    Preserves (Frame initial) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' holder_work_step initial

private theorem precompute_frame (pid : PeerId) (initial) :
    Preserves (Frame initial) (precomputeStaticStatic pid) := by
  unfold precomputeStaticStatic
  simp (config := {zeta := false}) only [requireNotPending,branch]
  repeat' holder_work_step initial

private theorem handshakeInit_frame (pid : PeerId) (psk : Option Key) (initial) :
    Preserves (Frame initial) (handshakeInit pid psk) := by
  unfold handshakeInit IndexOwner.setPeerWord
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head precomputeStaticStatic; exact precompute_frame _ initial)
    | holder_work_step initial


theorem publish_aligned (hi : holders.Aligned w) (o : Owner) (key : Key)
    (hd : w.dev.isSome = true) :
    (addBase holders o).Aligned
      {w with dev := w.dev.map fun d => {d with peerList := d.peerList ++ [o.slot], peerHashtable := (key,o.slot)::d.peerHashtable,numPeers := d.numPeers+1}} := by
  refine ⟨?_,?_,?_,?_,hi.cursor7,hi.cursor8⟩
  · cases dev : w.dev with
    | none => simp [dev] at hd
    | some d => simpa [addBase,dev] using congrArg (· ++ [o.slot]) hi.base
  · intro d found
    cases dev : w.dev with
    | none => simp [dev] at found
    | some before =>
      have same : d = {before with peerList := before.peerList ++ [o.slot], peerHashtable := (key,o.slot)::before.peerHashtable,numPeers := before.numPeers+1} := by
        simpa [dev] using found.symm
      subst d
      exact hi.send before dev
  · simpa [addBase,Option.map_map,Function.comp_def] using hi.clear
  · intro pid batches found
    exact hi.tx pid batches (by simpa [handoffTxView,Option.bind_map,Function.comp_def] using found)

theorem finish_aligned (pid : PeerId) (key : Key) (psk : Option Key)
    (hi : holders.Aligned w) (o : Owner) (slot : o.slot = pid)
    (hc : CarrierState cs (o :: loans) w)
    (a b : Ambient)
    (run : ((BaseCreation.finish pid key psk).run w).run a = .ok (((),v),b)) :
    (addBase holders o).Aligned v := by
  unfold BaseCreation.finish at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,x,ax,hx,rest⟩ := run; cases u
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,y,ay,hy,rest⟩ := rest; cases u
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,z,az,hz,done⟩ := rest; cases u
  have fx := (hoare_iff_run_ambient _ _ _).mp (dstCacheReset_frame pid w) w a () x ax (Frame.refl w) hx
  have fy := (hoare_iff_run_ambient _ _ _).mp (handshakeInit_frame pid psk x) x ax () y ay (Frame.refl x) hy
  have fz := (hoare_iff_run_ambient _ _ _).mp (resetLast_frame pid y) y ay () z az (Frame.refl y) hz
  have present : z.dev.isSome = true := by
    obtain ⟨p,hp,_⟩ := protected_resident hc.funded (by simp [demand]; omega : 0 < demand cs (o :: loans) o)
    obtain ⟨d,hd,_,_,_⟩ := resident_fields hp
    have base := (fx.trans (fy.trans fz)).send
    cases hzdev : z.dev with
    | none => simp [sendView,hd,hzdev] at base
    | some d => rfl
  cases done
  simpa only [slot] using publish_aligned (hi.frame (fx.trans (fy.trans fz))) o key present


/-- Actual successful creation funds and publishes one new base occurrence.
Normal errno returns preserve the old account; source failure arms remain. -/
theorem peerCreate_funded (key : Key) (psk : Option Key)
    (hi : holders.Funded cs loans w) (hs : StableRx cs w)
    (configured : ConfiguredIdentity.Inv w) (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    match result with
    | .error _ => holders.Funded cs loans v ∧ StableRx cs v
    | .ok pid => ∃ d, w.dev = some d ∧ pid = d.nextPeer ∧
        (addBase holders (BaseCreation.owner w d)).Funded cs loans v ∧ StableRx cs v := by
  let Q := fun (r : Except Int PeerId) (out : WGWorld) => match r with
    | .error _ => holders.Funded cs loans out ∧ StableRx cs out
    | .ok pid => ∃ d, w.dev = some d ∧ pid = d.nextPeer ∧
        (addBase holders (BaseCreation.owner w d)).Funded cs loans out ∧ StableRx cs out
  have getter : Hoare getDev (fun u => u = w) (fun d u => u = w ∧ w.dev = some d) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u aa d out bb hu hr
    subst u
    cases hd : w.dev with
    | none => simp [getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
    | some before =>
      simp [getDev,hd] at hr
      rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩
      exact ⟨rfl,rfl⟩
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
        exact ⟨hi,hs⟩
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
              (fun _ u => w.dev = some d ∧ holders.Aligned u ∧
                CarrierState cs (BaseCreation.owner w d :: (holders.owners ++ loans)) u ∧ StableRx cs u) := by
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro u aa x out bb h hr
            rcases h with ⟨rfl,hd⟩
            cases x
            have fact := BaseCreation.core_normal hi.carriers hs configured hd key aa bb hr
            rw [Peers.peerCreateCore_run] at hr
            cases hr
            exact ⟨hd,core_aligned hi hd (BaseCreation.frontier_vacant configured hd) key,fact.1,fact.2.1⟩
          apply hoare_bind _ _ core
          intro _
          have tail : Hoare (BaseCreation.finish d.nextPeer key psk)
              (fun u => w.dev = some d ∧ holders.Aligned u ∧
                CarrierState cs (BaseCreation.owner w d :: (holders.owners ++ loans)) u ∧ StableRx cs u)
              (fun _ u => Q (.ok d.nextPeer) u) := by
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro u aa x out bb h hr
            cases x
            obtain ⟨hc,hstable,_⟩ := BaseCreation.finish_funded d.nextPeer key psk h.2.2.1 h.2.2.2 aa bb hr
            have aligned := finish_aligned d.nextPeer key psk h.2.1 (BaseCreation.owner w d) rfl h.2.2.1 aa bb hr
            refine ⟨d,h.1,rfl,⟨aligned,WorkReservations.carrier_loans_perm hc ?_⟩,hstable⟩
            exact ((addBase_owners holders (BaseCreation.owner w d)).append_right loans).symm
          apply hoare_bind _ _ tail
          intro _
          apply hoare_consequence (hoare_pure (Except.ok d.nextPeer : Except Int PeerId) _)
          · exact fun _ h => h
          · intro r u h; rcases h with ⟨rfl,h⟩; exact h
  have out := (hoare_iff_run_ambient _ _ _).mp proof w a result v b rfl run
  cases result <;> exact out


theorem peerCreate_boundary (key : Key) (psk : Option Key)
    (hi : Boundary cs loans w) (configured : ConfiguredIdentity.Inv w)
    (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    Boundary cs loans v := by
  obtain ⟨holders,funded,stable⟩ := hi
  have post := peerCreate_funded key psk funded stable configured a b run
  cases result with
  | error e => exact ⟨holders,post⟩
  | ok pid => obtain ⟨d,_,_,funded,stable⟩ := post; exact ⟨addBase holders (BaseCreation.owner w d),funded,stable⟩

/-- The existing combined lifetime observer has the same creation endpoint. -/
theorem peerCreate_observed (key : Key) (psk : Option Key)
    (hi : Boundary cs loans w) (configured : ConfiguredIdentity.Inv w)
    (a b : Ambient) (history : List LifetimeEvent)
    (run : (runStatePrefix (peerCreateMixed key psk) w a history).1 = .ok ((result,v),b)) :
    Boundary cs loans v :=
  peerCreate_boundary key psk hi configured a b
    ((peerCreateMixed_erases key psk w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.HolderCreation
