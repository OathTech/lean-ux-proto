import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialSelection
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryBase

/-! Native observer contracts carrying an additional local state predicate.
The journal proof uses the action's exact erasure only for its state frame;
all emitted AEAD positions remain checked in that same source journal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

def With (P : WGWorld → Prop) (h : List Journal.Event) (w : WGWorld) (_ : Ambient) : Prop :=
  JournalInv h w ∧ P w

abbrev StateSafe (g : WGPrefix Journal.Event α) :=
  StatePrefixPreserves (fun h w _ => JournalInv h w) Safe g

theorem Safe.quiet_suffix (old : Safe h) (quiet : suffix.filterMap Journal.encryption? = []) :
    Safe (h ++ suffix) := by
  apply old.append
  intro pre e post position
  have member : e ∈ suffix := by rw [position]; simp
  cases e <;> simp only [Checked]
  rename_i r
  have found : r ∈ suffix.filterMap Journal.encryption? := List.mem_filterMap.mpr ⟨.encrypted r,member,rfl⟩
  rw [quiet] at found
  cases found

theorem state_quiet_extra {g : WGPrefix Journal.Event α} {action : WG.M α}
    {P : WGWorld → Prop} {Q : α → WGWorld → Prop}
    (app : StateAppends g) (quiet : StateHistoryFrame Journal.encryption? g)
    (erase : ErasesStatePrefix g action)
    (native : ∀ h, Hoare action (fun w => Inv h w ∧ P w) (fun x w => Inv h w ∧ Q x w)) :
    StatePrefixEnsures (With P) Safe g (fun x => With (Q x)) := by
  intro w a h hi
  obtain ⟨suffix,eq⟩ := app w a h
  have noCipher : suffix.filterMap Journal.encryption? = [] := by
    have same := quiet w a h
    rw [eq,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap Journal.encryption? with
    | nil => rfl
    | cons e es =>
      simp only [List.length_append,found,List.length_cons] at lengths
      omega
  have safe : Safe (runPrefix (g.run w) a h).2 := by rw [eq]; exact hi.1.2.quiet_suffix noCipher
  refine ⟨suffix,eq,safe,?_⟩
  cases result : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok value =>
    obtain ⟨⟨out,v⟩,b⟩ := value
    have run : (action.run w).run a = .ok ((out,v),b) := (erase w a h).symm.trans result
    have kept := (hoare_iff_run_ambient _ _ _).mp (native h) w a out v b ⟨hi.1.1,hi.2⟩ run
    refine ⟨⟨kept.1.mono ?_,safe⟩,kept.2⟩
    intro e member
    rw [eq]
    exact List.mem_append_left _ member

theorem state_quiet {g : WGPrefix Journal.Event α} {action : WG.M α}
    (app : StateAppends g) (quiet : StateHistoryFrame Journal.encryption? g)
    (erase : ErasesStatePrefix g action) (native : ∀ h, Preserves (Inv h) action) : StateSafe g := by
  apply (state_quiet_extra (P := fun _ => True) (Q := fun _ _ => True) app quiet erase ?_).consequence
    (fun _ _ _ hi => ⟨hi,True.intro⟩) (fun _ _ _ _ hi => hi.1)
  intro h
  exact hoare_consequence (native h) (fun _ hi => hi.1) (fun _ _ hi => ⟨hi,True.intro⟩)

theorem state_lift (action : WG.M α) (native : ∀ h, Preserves (Inv h) action) :
    StateSafe (liftWGPrefix action) :=
  state_quiet (StateAppends.lift _) (fun _ => HistoryFrame.lift _ _)
    (erasesStatePrefix_lift _) native

theorem state_extra (action : WG.M α) (native : ∀ h, Preserves (Inv h) action)
    (extra : Hoare action P Q) :
    StatePrefixEnsures (With P) Safe (liftWGPrefix action) (fun x => With (Q x)) := by
  apply state_quiet_extra (StateAppends.lift _) (fun _ => HistoryFrame.lift _ _)
    (erasesStatePrefix_lift _)
  intro h
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (native h) w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp extra w a x v b hi.2 run⟩

theorem selection (pid : PeerId) :
    StatePrefixEnsures (With CurrentSlots.Inv) Safe (Journal.selection pid) (fun x => With (Selected x)) := by
  apply state_quiet_extra (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((DriverCuts.selection pid).run w))
    (focusStatePrefix_erases _ _ (DriverCuts.selection_erases pid))
  intro h
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (NativeFrames.selection pid) w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp (selection_bound pid) w a x v b hi.2 run⟩

theorem reservation_extra (kid : KeypairId) (extra : Preserves P (Nonce.reserveNative kid)) :
    StatePrefixPreserves (With P) Safe (Journal.reserve kid) := by
  apply state_quiet_extra ((StateAppends.focus _ _ _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved
      (fun w => focusPrefix_other Journal.Event.nonce Journal.nonce? Journal.encryption? (fun _ => rfl)
        ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl))
    (receiptWGObserved_erases (focusStatePrefix_erases _ _ (Nonce.reserveObserved_erases kid)) _)
  intro h
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (NativeFrames.reservation kid) w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp extra w a x v b hi.2 run⟩

theorem reservation (kid : KeypairId) : StatePrefixPreserves (With (Pick kid)) Safe (Journal.reserve kid) :=
  reservation_extra kid (pick_reservation kid)

theorem creation (pid : PeerId) (item : List SkbId) : StateSafe (Journal.create pid item) := by
  apply state_quiet
  · intro w a h
    exact Appends.focus Journal.Event.disposition Journal.disposition? (TxDisposition.create pid item)
      (NativeAdapter.world w a) h
  · intro w a h
    exact focusPrefix_other Journal.Event.disposition Journal.disposition? Journal.encryption?
      (fun _ => rfl) (TxDisposition.create pid item) (NativeAdapter.world w a) h
  · exact NativeAdapter.lower_erases
      (focusPrefix_erases _ _ (TxDisposition.create_erases pid item))
  · exact fun _ => NativeFrames.create pid item

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
