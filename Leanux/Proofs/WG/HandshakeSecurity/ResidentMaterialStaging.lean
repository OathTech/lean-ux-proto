import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialState
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral

/-! The native staged-send callback derives allocation inputs from its actual
selected current slot and resident key read. The loop distinguishes early
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

def Accumulating (kid : KeypairId) (packets : List DataPacket) (w : WGWorld) : Prop :=
  Pick kid w ∧ ∀ packet ∈ packets, packet.keypair = kid

def Accumulated (kid : KeypairId) (acc : Option Unit × List DataPacket)
    (h : List Journal.Event) (w : WGWorld) (_ : Ambient) : Prop :=
  JournalInv h w ∧ (acc.1 = none → Accumulating kid acc.2 w)

private theorem accumulating_frame {action : WG.M α} (frame : Preserves (Pick kid) action) :
    Preserves (Accumulating kid packets) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp frame w a x v b hi.1 run,hi.2⟩

private theorem read_key (kid : KeypairId) :
    StatePrefixEnsures (With (Lower (kid + 1))) Safe (liftWGPrefix (getKeypair kid))
      (fun _ => With (Pick kid)) :=
  state_extra _ (fun _ => NativeFrames.read_key kid) (key_pick kid)

private theorem accepted (pid kid : Nat) (peer : Peer) :
    StatePrefixEnsures (With (Pick kid)) Safe
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
    (P := With (Accumulating kid [])) (Q := fun _ h w _ => JournalInv h w)
  · apply StatePrefixEnsures.bind (Q := Accumulated kid)
    · apply forIn_exit peer.staged (none,[]) _
        (fun acc => With (Accumulating kid acc.2)) (Accumulated kid)
        (fun _ _ _ _ hi => hi.1.2) (fun _ _ _ _ hi => ⟨hi.1,fun _ => hi.2⟩)
      intro pkt acc
      apply StatePrefixEnsures.bind (ambient _)
      intro _
      apply StatePrefixEnsures.bind (state_extra _ (fun _ => (ipTunnelEcnEncap_sameWGWorld pkt).wp (Inv _))
        (accumulating_frame ((ipTunnelEcnEncap_sameWGWorld pkt).wp (Pick kid))))
      intro ds
      apply StatePrefixEnsures.bind (reservation_extra kid (accumulating_frame (pick_reservation kid)))
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
          rfl
    · intro acc
      obtain ⟨done,packets⟩ := acc
      cases done with
      | some out => exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1.2) (fun _ _ _ hi => hi.1)
      | none =>
        apply StatePrefixEnsures.consequence (P := With (Accumulating kid packets))
        · apply StatePrefixEnsures.bind (ambient _)
          intro _
          apply StatePrefixEnsures.bind (state_extra _ (fun _ => indexOwner_peerDeref_preserves _ _)
            (indexOwner_peerDeref_preserves _ _))
          intro owner
          apply StatePrefixEnsures.bind (state_extra _ (fun _ => NativeFrames.peer_get owner)
            (accumulating_frame (pick_frame (pool_of_material (Origins.Retaining.peerGet_material owner))
              (lower_metadata (peerGet_metadata owner)))))
          intro _
          apply StatePrefixEnsures.bind ((allocate packets).consequence
            (fun _ _ _ hi => ⟨hi.1,hi.2.1.inputs hi.2.2⟩) (fun _ _ _ _ hi => hi))
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
  simp only [Driver.noKey_lift Journal.hooks rfl]
  dsimp only [Journal.hooks]
  apply StatePrefixEnsures.bind (selection pid)
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
        apply StatePrefixEnsures.bind ((read_key kid).consequence
          (fun _ _ _ hi => ⟨hi.1,hi.2 peer kid rfl⟩) (fun _ _ _ _ hi => hi))
        intro key
        apply StatePrefixEnsures.bind (ambient _)
        intro invalid
        split
        · exact out _ false
        · apply StatePrefixEnsures.bind (state_extra _ (fun _ => (branchExpired_sameWGWorld _ _ _ _).wp (Inv _))
            ((branchExpired_sameWGWorld _ _ _ _).wp (Pick kid)))
          intro expired
          split
          · exact out _ true
          · exact accepted pid kid peer

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
