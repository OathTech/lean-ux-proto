import Leanux.Proofs.WG.HandshakeSecurity.StagingOwnerState
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral

/-! The native staged-send callback derives allocation inputs from its actual
selected current slot, resident key read and successful owner dereference.
The loop distinguishes early
refusal from continued accumulation, since refusal may release the last key. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem forIn_exit (xs : List α) (b : β)
    (g : α → β → WGPrefix Journal.Event (ForInStep β))
    (I Q : β → List Journal.Event → WGWorld → Ambient → Prop)
    (safe : ∀ b h w a, Q b h w a → Safe h)
    (finish : ∀ b h w a, I b h w a → Q b h w a)
    (body : ∀ x b, StatePrefixEnsures (I b) Safe (g x b)
      (fun step => match step with | .done out => Q out | .yield out => I out)) :
    StatePrefixEnsures (I b) Safe (forIn xs b g) Q := by
  induction xs generalizing b with
  | nil =>
    exact StatePrefixEnsures.pure b (fun h w a hi => safe b h w a (finish b h w a hi)) (finish b)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StatePrefixEnsures.bind (body x b)
    intro step
    cases step with
    | done out => exact StatePrefixEnsures.pure out (safe out) (fun _ _ _ hi => hi)
    | yield out => exact ih out

private theorem ambient (action : AmbientM α) :
    StatePrefixPreserves (With P) Safe (liftWGPrefix (monadLift action)) :=
  state_extra _ (fun _ => hoare_liftAmbient _ _) (hoare_liftAmbient _ _)

private theorem forget {g : WGPrefix Journal.Event α} (safe : StateSafe g) :
    StatePrefixEnsures (With P) Safe g (fun _ h w _ => JournalInv h w) :=
  safe.consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

private theorem pure_result (value : α) :
    StatePrefixEnsures (With P) Safe (pure value) (fun _ h w _ => JournalInv h w) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1.2) (fun _ _ _ hi => hi.1)

def Accumulating (pid : PeerId) (kid : KeypairId) (packets : List DataPacket) (w : WGWorld) : Prop :=
  OwnerPick pid kid w ∧ ∀ packet ∈ packets, packet.keypair = kid ∧ packet.peer = pid

def Accumulated (pid : PeerId) (kid : KeypairId) (acc : Option Unit × List DataPacket)
    (h : List Journal.Event) (w : WGWorld) (_ : Ambient) : Prop :=
  JournalInv h w ∧ (acc.1 = none → Accumulating pid kid acc.2 w)

private theorem accumulating_frame {action : WG.M α} (frame : Preserves (OwnerPick pid kid) action) :
    Preserves (Accumulating pid kid packets) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp frame w a x v b hi.1 run,hi.2⟩

private theorem read_key (pid : PeerId) (kid : KeypairId) :
    StatePrefixEnsures (With (fun w => Lower (kid + 1) w ∧ RxCredits.KeyCompatible pid kid w)) Safe (liftWGPrefix (getKeypair kid))
      (fun _ => With (OwnerPick pid kid)) :=
  state_extra _ (fun _ => NativeFrames.read_key kid) (owner_pick_read pid kid)

private theorem dereference (pid kid : Nat) (packets : List DataPacket) :
    Hoare (IndexOwner.peerDeref (.keypair kid)) (Accumulating pid kid packets)
      (fun _ w => Accumulating pid kid packets w ∧
        RxCredits.keyWords w kid = some (some pid)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a owner v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
      (indexOwner_peerDeref_preserves _ _) w a owner v b before run,
    ((hoare_iff_run_ambient _ _ _).mp (dereference_owner pid kid)
      w a owner v b before.1.2 run).2⟩

private theorem acquired (pid kid owner : Nat) (packets : List DataPacket) :
    Preserves (fun w => Accumulating pid kid packets w ∧
      RxCredits.keyWords w kid = some (some pid)) (peerGet owner) := by
  have pick : Preserves (Pick kid) (peerGet owner) :=
    pick_frame (pool_of_material (Origins.Retaining.peerGet_material owner))
      (lower_metadata (peerGet_metadata owner))
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have words := (ProjectedAction.iff_run_ambient _ _ _).mp
    (RxCredits.peerGet_words owner) w a result v b run
  refine ⟨⟨⟨?_,?_⟩,before.1.2⟩,?_⟩
  · exact (hoare_iff_run_ambient _ _ _).mp pick w a result v b before.1.1.1 run
  · exact (hoare_iff_run_ambient _ _ _).mp
      (RxCredits.keyWords_keep (RxCredits.peerGet_words owner) pid kid)
      w a result v b before.1.1.2 run
  · rw [words]
    exact before.2

private theorem accepted (pid kid : Nat) (peer : Peer) :
    StatePrefixEnsures (With (OwnerPick pid kid)) Safe
      (do
        let mut packetsCb : List DataPacket := []
        for pkt in peer.staged do
          _ ← liftWGPrefix (branch .stagedNonceIterate true)
          let ds ← liftWGPrefix (ipTunnelEcnEncap pkt)
          let nonce ← Journal.reserve kid
          if ← liftWGPrefix (branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then
            return ← liftWGPrefix (stagedOutNokey pid peer.staged (some kid) true)
          packetsCb := packetsCb ++ [{peer := pid,keypair := kid,nonce,plaintext := pkt,ds}]
        _ ← liftWGPrefix (branch .stagedNonceIterate false)
        liftWGPrefix (peerGet (← liftWGPrefix (IndexOwner.peerDeref (.keypair kid))))
        let item ← Journal.allocate packetsCb
        Journal.create pid item)
      (fun _ h w _ => JournalInv h w) := by
  apply StatePrefixEnsures.consequence
    (P := With (Accumulating pid kid [])) (Q := fun _ h w _ => JournalInv h w)
  · apply StatePrefixEnsures.bind (Q := Accumulated pid kid)
    · apply forIn_exit peer.staged (none,[]) _
        (fun acc => With (Accumulating pid kid acc.2)) (Accumulated pid kid)
        (fun _ _ _ _ hi => hi.1.2) (fun _ _ _ _ hi => ⟨hi.1,fun _ => hi.2⟩)
      intro pkt acc
      apply StatePrefixEnsures.bind (ambient _)
      intro _
      apply StatePrefixEnsures.bind (state_extra _ (fun _ => (ipTunnelEcnEncap_sameWGWorld pkt).wp (Inv _))
        (accumulating_frame ((ipTunnelEcnEncap_sameWGWorld pkt).wp (OwnerPick pid kid))))
      intro ds
      apply StatePrefixEnsures.bind (reservation_extra kid (accumulating_frame (owner_pick_reservation pid kid)))
      intro nonce
      apply StatePrefixEnsures.bind (ambient _)
      intro rejected
      split
      · apply StatePrefixEnsures.bind (forget (state_lift _ (fun _ => NativeFrames.no_key pid peer.staged (some kid) true)))
        intro out
        exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => ⟨hi,by intro impossible; cases impossible⟩)
      · apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1.2)
        intro h w a hi
        refine ⟨hi.1,hi.2.1,?_⟩
        intro packet member
        rcases List.mem_append.mp member with old | fresh
        · exact hi.2.2 packet old
        · have same := List.mem_singleton.mp fresh
          subst packet
          exact ⟨rfl,rfl⟩
    · intro acc
      obtain ⟨done,packets⟩ := acc
      cases done with
      | some out => exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1.2) (fun _ _ _ hi => hi.1)
      | none =>
        apply StatePrefixEnsures.consequence (P := With (Accumulating pid kid packets))
        · apply StatePrefixEnsures.bind (ambient _)
          intro _
          apply StatePrefixEnsures.bind (state_extra _ (fun _ => indexOwner_peerDeref_preserves _ _)
            (dereference pid kid packets))
          intro owner
          apply StatePrefixEnsures.bind (state_extra _ (fun _ => NativeFrames.peer_get owner)
            (acquired pid kid owner packets))
          intro _
          apply StatePrefixEnsures.bind ((allocate packets).consequence
            (fun _ _ _ hi => ⟨hi.1,hi.2.1.1.1.inputs hi.2.2 hi.2.1.2⟩) (fun _ _ _ _ hi => hi))
          intro items
          exact creation pid items
        · exact fun _ _ _ hi => ⟨hi.1,hi.2 rfl⟩
        · exact fun _ _ _ _ hi => hi
  · exact fun _ _ _ hi => ⟨hi.1,hi.2,by simp⟩
  · exact fun _ _ _ _ hi => hi

/-- Complete native staging supplies the packet-allocation precondition from
its selected current slot. This local contract exposes only C1 slot safety;
initialized transport is a separate caller obligation. -/
theorem staging (pid : PeerId) :
    StatePrefixEnsures (With CurrentSlots.Inv) Safe (Driver.stagingObserved Journal.hooks pid)
      (fun _ h w _ => JournalInv h w) := by
  unfold Driver.stagingObserved
  simp only [Driver.restore_noKey_lift Journal.hooks rfl rfl rfl]
  dsimp only [Journal.hooks]
  apply StatePrefixEnsures.bind (owner_selection pid)
  intro chosen
  cases chosen with
  | none => exact pure_result _
  | some pair =>
    obtain ⟨peer,kp⟩ := pair
    have out (P : WGWorld → Prop) (invalid : Bool) := forget (P := P) (state_lift _ (fun _ => NativeFrames.no_key pid peer.staged kp invalid))
    apply StatePrefixEnsures.bind (ambient _)
    intro missing
    split
    · exact out _ false
    · cases kp with
      | none => exact forget (state_lift _ (fun _ => hoare_liftAmbient (AmbientM.invariant _) _))
      | some kid =>
        apply StatePrefixEnsures.bind ((read_key pid kid).consequence
          (fun _ _ _ hi => ⟨hi.1,hi.2 peer kid rfl⟩) (fun _ _ _ _ hi => hi))
        intro key
        apply StatePrefixEnsures.bind (ambient _)
        intro invalid
        split
        · exact out _ false
        · apply StatePrefixEnsures.bind (state_extra _ (fun _ => (branchExpired_sameWGWorld _ _ _ _).wp (Inv _))
            ((branchExpired_sameWGWorld _ _ _ _).wp (OwnerPick pid kid)))
          intro expired
          split
          · exact out _ true
          · exact accepted pid kid peer

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
