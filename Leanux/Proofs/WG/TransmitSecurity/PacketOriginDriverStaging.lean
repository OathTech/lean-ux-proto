import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginEventFrames
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginStagingFrames
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryBase

/-! The shared staging source preserves packet provenance: reservation and
selection leave stored TX material intact, allocation supplies its origin,
and both native queue-refusal branches retain certificates of survivors. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

abbrev StateSafe (g : WGPrefix Journal.Event α) :=
  StatePrefixPreserves (fun h w _ => JournalInv h w) Safe g

theorem Safe.quiet_suffix (old : Safe h) (quiet : suffix.filterMap watched? = []) :
    Safe (h ++ suffix) := by
  apply old.append
  intro pre e post position
  have member : e ∈ suffix := by rw [position]; simp
  apply checked_quiet
  cases found : watched? e with
  | none => rfl
  | some value =>
    have present : value ∈ suffix.filterMap watched? := List.mem_filterMap.mpr ⟨e,member,found⟩
    rw [quiet] at present
    cases present

theorem state_quiet {g : WGPrefix Journal.Event α} {action : WG.M α}
    (app : StateAppends g) (quiet : StateHistoryFrame watched? g)
    (erase : ErasesStatePrefix g action) (native : ∀ h, Preserves (Inv h) action) : StateSafe g := by
  intro w a h hi
  obtain ⟨suffix,eq⟩ := app w a h
  have noCipher : suffix.filterMap watched? = [] := by
    have same := quiet w a h
    rw [eq,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap watched? with
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
    have kept := (hoare_iff_run_ambient _ _ _).mp (native h) w a out v b hi.1 run
    refine ⟨kept.mono ?_,safe⟩
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
      (fun w => focusPrefix_other Journal.Event.nonce Journal.nonce? watched? (fun _ => rfl)
        ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl))
    (receiptWGObserved_erases (focusStatePrefix_erases _ _ (Nonce.reserveObserved_erases kid)) _)
    (fun _ => NativeFrames.reservation kid)

theorem creation (pid : PeerId) (item : List SkbId) : StateSafe (Journal.create pid item) := by
  apply state_quiet
  · intro w a h
    exact Appends.focus Journal.Event.disposition Journal.disposition? (TxDisposition.create pid item)
      (NativeAdapter.world w a) h
  · intro w a h
    exact creation_watched pid item (NativeAdapter.world w a) h
  · exact NativeAdapter.lower_erases
      (focusPrefix_erases _ _ (TxDisposition.create_erases pid item))
  · exact fun _ => NativeFrames.create pid item

private theorem state_loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → WGPrefix Journal.Event (ForInStep β)) (safe : ∀ x b, StateSafe (g x b)) :
    StateSafe (forIn xs b g) :=
  StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => JournalInv h w) Safe
    (fun _ _ _ _ hi => hi.2) safe

macro "origin_driver_step" : tactic => `(tactic| first
  | (nonce_source_head getPeer; exact state_lift _ (fun _ => NativeFrames.read_peer _))
  | (nonce_source_head getKeypair; exact state_lift _ (fun _ => NativeFrames.read_key _))
  | (nonce_source_head getDev; exact state_lift _ (fun _ => NativeFrames.store getDev_sameWGStore))
  | (nonce_source_head setPeer; exact state_lift _ (fun _ => frame (PacketOrigins.modify _ (fun _ => rfl) (fun _ => rfl))))
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

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved Journal.hooks pid) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold Driver.stagingObserved
  simp only [Driver.restore_noKey_lift Journal.hooks rfl rfl rfl]
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
          · try dsimp only
            repeat' first
              | (nonce_source_head Journal.reserve; exact reservation _)
              | (nonce_source_head Journal.allocate; exact allocate _)
              | (nonce_source_head Journal.create; exact creation _ _)
              | origin_driver_step

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved Journal.hooks pid) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  rw [Driver.keepalive_native _ rfl]
  unfold Driver.keepaliveInline
  repeat' first
    | (nonce_source_head Driver.stagingObserved; exact staging _)
    | origin_driver_step

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
