import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral
import Leanux.Proofs.WG.TransmitSecurity.JournalCiphertextOrigins
import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginStagingFrames
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryBase

/-! The shared staging source preserves packet provenance: reservation and
selection leave stored TX material intact, allocation supplies empty wire buffers,
and both native queue-refusal branches retain certificates of survivors. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

abbrev StateSafe (g : WGPrefix Journal.Event α) :=
  StatePrefixPreserves (fun h w _ => JournalInv h w) Safe g

theorem state_quiet {g : WGPrefix Journal.Event α} {action : WG.M α}
    (app : StateAppends g) (quiet : StateHistoryFrame Journal.SocketHistory.socket? g)
    (erase : ErasesStatePrefix g action) (native : ∀ h, Preserves (Inv h) action) : StateSafe g := by
  intro w a h hi
  obtain ⟨suffix,eq⟩ := app w a h
  have noCipher : suffix.filterMap Journal.SocketHistory.socket? = [] := by
    have same := quiet w a h
    rw [eq,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap Journal.SocketHistory.socket? with
    | nil => rfl
    | cons e es =>
      simp only [List.length_append,found,List.length_cons] at lengths
      omega
  have safe : Safe (runPrefix (g.run w) a h).2 := by rw [eq]; exact hi.2.quiet_suffix noCipher
  refine ⟨suffix,eq,safe,?_⟩
  cases result : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok value =>
    obtain ⟨⟨out,v⟩,b⟩ := value
    have run : (action.run w).run a = .ok ((out,v),b) := (erase w a h).symm.trans result
    have kept := (hoare_iff_run_ambient _ _ _).mp (native (receipts h)) w a out v b hi.1 run
    refine ⟨kept.mono (receipts_mono ?_),safe⟩
    intro e member
    rw [eq]
    exact List.mem_append_left _ member

theorem state_lift (action : WG.M α) (native : ∀ h, Preserves (Inv h) action) :
    StateSafe (liftWGPrefix action) :=
  state_quiet (StateAppends.lift _) (fun _ => HistoryFrame.lift _ _)
    (erasesStatePrefix_lift _) native

theorem selection (pid : PeerId) : StateSafe (Journal.selection pid) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((HandshakeSecurity.Responder.DriverCuts.selection pid).run w))
    (focusStatePrefix_erases _ _ (HandshakeSecurity.Responder.DriverCuts.selection_erases pid))
    (fun _ => NativeFrames.selection pid)

theorem reservation (kid : KeypairId) : StateSafe (Journal.reserve kid) :=
  state_quiet ((StateAppends.focus _ _ _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved
      (fun w => focusPrefix_other Journal.Event.nonce Journal.nonce? Journal.SocketHistory.socket? (fun _ => rfl)
        ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl))
    (receiptWGObserved_erases (focusStatePrefix_erases _ _ (Nonce.reserveObserved_erases kid)) _)
    (fun _ => NativeFrames.reservation kid)

theorem creation (pid : PeerId) (item : List SkbId) : StateSafe (Journal.create pid item) := by
  apply state_quiet
  · intro w a h
    exact Appends.focus Journal.Event.disposition Journal.disposition? (TxDisposition.create pid item)
      (NativeAdapter.world w a) h
  · intro w a h
    exact focusPrefix_other Journal.Event.disposition Journal.disposition? Journal.SocketHistory.socket?
      (fun _ => rfl) (TxDisposition.create pid item) (NativeAdapter.world w a) h
  · exact NativeAdapter.lower_erases
      (focusPrefix_erases _ _ (TxDisposition.create_erases pid item))
  · exact fun _ => NativeFrames.create pid item

private theorem state_loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → WGPrefix Journal.Event (ForInStep β)) (safe : ∀ x b, StateSafe (g x b)) :
    StateSafe (forIn xs b g) :=
  StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => JournalInv h w) Safe
    (fun _ _ _ _ hi => hi.2) safe

macro "ciphertext_driver_step" : tactic => `(tactic| first
  | (nonce_source_head getPeer; exact state_lift _ (fun _ => NativeFrames.read_peer _))
  | (nonce_source_head getKeypair; exact state_lift _ (fun _ => NativeFrames.read_key _))
  | (nonce_source_head getDev; exact state_lift _ (fun _ => NativeFrames.store getDev_sameWGStore))
  | (nonce_source_head setPeer; exact state_lift _ (fun _ => frame (CiphertextOrigins.modify _ (fun _ => rfl) (fun _ => rfl))))
  | (nonce_source_head peerGet; exact state_lift _ (fun _ => NativeFrames.peer_get _))
  | (nonce_source_head stagedOutNokey; exact state_lift _ (fun _ => NativeFrames.out _ _ _ _))
  | (nonce_source_head branchExpired; exact state_lift _ (fun _ => (branchExpired_sameWGWorld _ _ _ _).wp (Inv _)))
  | (nonce_source_head ipTunnelEcnEncap; exact state_lift _ (fun _ => (ipTunnelEcnEncap_sameWGWorld _).wp (Inv _)))
  | (nonce_source_head IndexOwner.peerDeref; exact state_lift _ (fun _ => indexOwner_peerDeref_preserves _ _))
  | (nonce_source_head branch; exact state_lift _ (fun _ => hoare_liftAmbient (AmbientM.branch _ _) _))
  | (nonce_source_head branchCmp; exact state_lift _ (fun _ => hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) _))
  | (nonce_source_head invariant; exact state_lift _ (fun _ => hoare_liftAmbient (AmbientM.invariant _) _))
  | (nonce_source_head hiddenAlloc; exact state_lift _ (fun _ => hoare_liftAmbient (AmbientM.hiddenAlloc _) _))
  | (nonce_source_head Pure.pure; exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi))
  | (nonce_source_head ForIn.forIn; apply state_loop; intro x b; change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | split
  | (with_reducible intro x; try dsimp only))

private theorem keep {g : WGPrefix Journal.Event α} (rule : StateSafe g) (C : Prop) :
    StatePrefixPreserves (fun h w _ => JournalInv h w ∧ C) Safe g := by
  intro w a h before
  obtain ⟨suffix,extension,safe,post⟩ := rule w a h before.1
  refine ⟨suffix,extension,safe,?_⟩
  cases run : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok out => exact ⟨by simpa only [run] using post,before.2⟩

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved Journal.hooks pid) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold Driver.stagingObserved
  simp only [Driver.noKey_lift Journal.hooks rfl]
  dsimp only [Journal.hooks]
  apply StatePrefixEnsures.bind (selection pid)
  intro selected
  cases selected with
  | none => exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi)
  | some pair =>
    obtain ⟨p,kp⟩ := pair
    have hout (invalid : Bool) := state_lift _ (fun _ => NativeFrames.out pid p.staged kp invalid)
    apply StatePrefixEnsures.bind (state_lift _ (fun _ => hoare_liftAmbient (AmbientM.branch _ _) _))
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact state_lift _ (fun _ => hoare_liftAmbient (AmbientM.invariant _) _)
      | some id =>
        apply StatePrefixEnsures.bind (state_lift _ (fun _ => NativeFrames.read_key id))
        intro k
        apply StatePrefixEnsures.bind (state_lift _ (fun _ => hoare_liftAmbient (AmbientM.branch _ _) _))
        intro invalid
        split
        · exact hout false
        · apply StatePrefixEnsures.bind (state_lift _ (fun _ => (branchExpired_sameWGWorld _ _ _ _).wp (Inv _)))
          intro expired
          split
          · exact hout true
          · apply StatePrefixEnsures.consequence
              (P := fun h w _ => JournalInv h w ∧ ∀ packet ∈ ([] : List DataPacket), packet.bytes = [])
            · apply StatePrefixEnsures.bind (Q := fun acc : Option Unit × List DataPacket =>
                  fun h w _ => JournalInv h w ∧ ∀ packet ∈ acc.2, packet.bytes = [])
              · apply StatePrefixEnsures.forInInvariant p.staged (none, []) _
                  (fun acc : Option Unit × List DataPacket =>
                    fun h w _ => JournalInv h w ∧ ∀ packet ∈ acc.2, packet.bytes = []) Safe
                  (fun _ _ _ _ hi => hi.1.2)
                intro pkt acc
                apply StatePrefixEnsures.bind (keep (state_lift _ (fun _ => hoare_liftAmbient (AmbientM.branch _ _) _)) _)
                intro _
                apply StatePrefixEnsures.bind (keep (state_lift _ (fun _ => (ipTunnelEcnEncap_sameWGWorld pkt).wp (Inv _))) _)
                intro ds
                apply StatePrefixEnsures.bind (keep (reservation id) _)
                intro nonce
                apply StatePrefixEnsures.bind (keep (state_lift _ (fun _ => hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) _)) _)
                intro rejected
                cases rejected with
                | true =>
                  apply StatePrefixEnsures.bind (keep (hout true) _)
                  intro result
                  exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1.2) (fun _ _ _ hi => hi)
                | false =>
                  apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1.2)
                  intro h w a hi
                  refine ⟨hi.1,?_⟩
                  intro packet member
                  rcases List.mem_append.mp member with old | new
                  · exact hi.2 packet old
                  · have same : packet = DataPacket.mk pid id nonce pkt ds .uncrypted [] := by simpa using new
                    subst packet
                    rfl
              · intro acc
                obtain ⟨done,packets⟩ := acc
                cases done with
                | some result => exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1.2) (fun _ _ _ hi => hi.1)
                | none =>
                  apply StatePrefixEnsures.bind (keep (state_lift _ (fun _ => hoare_liftAmbient (AmbientM.branch _ _) _)) _)
                  intro _
                  apply StatePrefixEnsures.bind (keep (state_lift _ (fun _ => indexOwner_peerDeref_preserves _ _)) _)
                  intro owner
                  apply StatePrefixEnsures.bind (keep (state_lift _ (fun _ => NativeFrames.peer_get owner)) _)
                  intro _ w a h before
                  exact StatePrefixEnsures.bind (allocate packets before.2)
                    (fun items => creation pid items) w a h before.1
            · intro h w a before
              exact ⟨before,by intro packet member; cases member⟩
            · exact fun _ _ _ _ hi => hi

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved Journal.hooks pid) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold Driver.keepaliveObserved
  repeat' first
    | (nonce_source_head Driver.stagingObserved; exact staging _)
    | ciphertext_driver_step

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
