import Leanux.Proofs.WG.Progress.AllocationSuffixSource
import Leanux.Proofs.Logged.WGPrefix
import Leanux.WG.RxData

/-! Native WG actions retain an ambient record suffix. The transport laws run the actual nested state stack; individual ambient leaves have explicit contracts. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

abbrev NativeKeeps (records : List HiddenRecord) {α : Type} (action : WG.M α) : Prop :=
  ∀ g, Preserves (fun a => Tail records a.hidden) (action.run g)

theorem native_pure {α : Type} (records : List HiddenRecord) (value : α) :
    NativeKeeps records (pure value) := fun _ => preserves_pure _

theorem native_bind {α β : Type} (records : List HiddenRecord)
    (action : WG.M α) (next : α → WG.M β)
    (first : NativeKeeps records action) (rest : ∀ x, NativeKeeps records (next x)) :
    NativeKeeps records (action >>= next) := by
  intro g
  rw [StateT.run_bind]
  exact preserves_bind (first g) (fun out => rest out.1 out.2)

theorem native_ambient {α : Type} (records : List HiddenRecord) (action : AmbientM α)
    (keep : Preserves (fun a => Tail records a.hidden) action) :
    NativeKeeps records (monadLift action) := by
  intro g
  change Preserves _ (action >>= fun value => pure (value,g))
  exact preserves_bind keep (fun value => preserves_pure _)

theorem native_get (records : List HiddenRecord) :
    NativeKeeps records (get : WG.M WGWorld) := fun _ => preserves_pure _

theorem native_modify (records : List HiddenRecord) (f : WGWorld → WGWorld) :
    NativeKeeps records (modify f) := fun _ => preserves_pure _

theorem native_stop {α : Type} (records : List HiddenRecord) (e : Stop) :
    NativeKeeps records (throw e : WG.M α) := fun _=>ambient_stop _ _

theorem native_statePrefix {E α : Type} (records : List HiddenRecord) (action : WG.M α)
    (keep : NativeKeeps records action) :
    StatePrefixPreserves (fun (_ : List E) _ a=>Tail records a.hidden) (fun _=>True)
      (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ _=>True.intro)
    (fun _ g a value after b pre run => (hoare_iff_run _ _ _).mp (keep g) a (value,after) b pre run)

theorem native_branch (records : List HiddenRecord) (decision : Decision) (value : Bool) :
    NativeKeeps records (branch decision value) := by
  apply native_ambient
  apply (hoare_iff_run _ _ _).mpr
  intro before out after pre run
  cases run; exact pre

theorem native_branchCmp (records : List HiddenRecord) (decision : Decision)
    (value : Bool) (left right : Int) :
    NativeKeeps records (branchCmp decision value left right) := by
  apply native_ambient
  apply (hoare_iff_run _ _ _).mpr
  intro before out after pre run
  cases run; exact pre

theorem native_hidden (records : List HiddenRecord) (site : HiddenSite) :
    NativeKeeps records (hidden site) :=
  native_ambient records _ (hoare_consequence (hidden_after_tail site records)
    (fun _ h=>h) (fun _ _ h=>strict_tail h))

theorem native_alloc (records : List HiddenRecord) (site : AllocSite) :
    NativeKeeps records (hiddenAlloc site) :=
  native_ambient records _ (hiddenAlloc_retains site records)

theorem native_getDev (records : List HiddenRecord) : NativeKeeps records getDev := by
  unfold getDev
  apply native_bind records _ _ (native_get records)
  intro g
  split
  · exact native_pure records _
  · exact native_stop records _

theorem native_modifyDev (records : List HiddenRecord) (f : Device → Device) :
    NativeKeeps records (modifyDev f) := native_modify records _

theorem native_getPeer (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (getPeer pid) := by
  unfold getPeer
  apply native_bind records _ _ (native_getDev records)
  intro d
  split
  · exact native_pure records _
  · exact native_stop records _

theorem native_setPeer (records : List HiddenRecord) (pid : PeerId) (p : Peer) :
    NativeKeeps records (setPeer pid p) := native_modifyDev records _

theorem native_getKeypair (records : List HiddenRecord) (kid : KeypairId) :
    NativeKeeps records (getKeypair kid) := by
  unfold getKeypair
  apply native_bind records _ _ (native_getDev records)
  intro d
  split
  · exact native_pure records _
  · exact native_stop records _

theorem native_setKeypair (records : List HiddenRecord) (kid : KeypairId) (k : Keypair) :
    NativeKeeps records (setKeypair kid k) := native_modifyDev records _

theorem native_clock (records : List HiddenRecord) (site : HiddenSite) :
    NativeKeeps records (hiddenClock64 site) := by
  apply native_ambient
  unfold AmbientM.hiddenClock64
  apply preserves_bind (hoare_consequence (hidden_after_tail site records)
    (fun _ h=>h) (fun _ _ h=>strict_tail h))
  intro bytes
  exact preserves_pure _

theorem native_birthdate (records : List HiddenRecord) (birthday : Int64) (seconds : Nat) :
    NativeKeeps records (birthdateTest birthday seconds) := by
  unfold birthdateTest
  exact native_bind records _ _ (native_clock records _) (fun _=>native_pure records _)

theorem native_expired (records : List HiddenRecord) (decision : Decision)
    (birthday : Int64) (seconds : Nat) (f : Bool → Bool) :
    NativeKeeps records (branchExpired decision birthday seconds f) := by
  unfold branchExpired
  exact native_bind records _ _ (native_birthdate records _ _) (fun _=>native_branchCmp records _ _ _ _)

theorem native_or (records : List HiddenRecord) (left right : WG.M Bool)
    (hl : NativeKeeps records left) (hr : NativeKeeps records right) :
    NativeKeeps records (WG.orM left right) := by
  unfold WG.orM
  apply native_bind records _ _ hl
  intro b
  cases b
  · exact hr
  · exact native_pure records _

theorem native_invariant {α : Type} (records : List HiddenRecord) (message : String) :
    NativeKeeps records (invariant message : WG.M α) := native_stop records _

theorem native_unsupported {α : Type} (records : List HiddenRecord) (message : String) :
    NativeKeeps records (unsupported message : WG.M α) := by
  apply native_ambient
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  cases run

theorem native_liftSkb {α : Type} (records : List HiddenRecord) (action : SkbM α)
    (keep : ∀ s, Preserves (fun a => Tail records a.hidden) (action.run s)) :
    NativeKeeps records (liftSkb action) := by
  unfold liftSkb
  apply native_bind records _ _ (native_getDev records)
  intro d
  apply native_bind records _ _ (native_ambient records _ (keep _))
  intro out
  exact native_bind records _ _ (native_modifyDev records _) (fun _=>native_pure records _)

theorem native_getRx (records : List HiddenRecord) (id : SkbId) :
    NativeKeeps records (getRxSkb id) := by
  apply native_liftSkb
  intro s
  unfold SkbStore.getRx
  simp only [StateT.run_bind,StateT.run_get,pure_bind]
  split
  · exact preserves_pure _
  · exact ambient_stop _ _

theorem native_setRx (records : List HiddenRecord) (id : SkbId) (f : RxPacket → RxPacket) :
    NativeKeeps records (setRxSkb id f) := by
  apply native_liftSkb
  intro s
  unfold SkbStore.setRx SkbStore.getRx
  simp only [StateT.run_bind,StateT.run_get,pure_bind]
  split
  · exact preserves_pure _
  · exact ambient_stop _ _

theorem native_refcountInc (records : List HiddenRecord) (count : Nat) :
    NativeKeeps records (refcountInc count : WG.M Unit) := by
  unfold refcountInc
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_branchCmp records _ _ _ _
    | with_reducible exact native_unsupported records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem native_peerGet (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (peerGet pid) := by
  unfold peerGet requireNotPending
  repeat' first
    | with_reducible exact native_getPeer records _
    | with_reducible exact native_setPeer records _ _
    | with_reducible exact native_refcountInc records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | (with_reducible intro x; try dsimp only)

theorem native_peerWord (records : List HiddenRecord) (owner : IndexOwner) :
    NativeKeeps records owner.peerWord := by
  cases owner <;> unfold IndexOwner.peerWord
  · exact native_bind records _ _ (native_getPeer records _) (fun _=>native_pure records _)
  · exact native_bind records _ _ (native_getKeypair records _) (fun _=>native_pure records _)

theorem native_peerDeref (records : List HiddenRecord) (owner : IndexOwner) :
    NativeKeeps records owner.peerDeref := by
  unfold IndexOwner.peerDeref
  apply native_bind records _ _ (native_peerWord records owner)
  intro peer
  split
  · exact native_pure records _
  · exact native_unsupported records _

theorem native_product {α : Type} (records : List HiddenRecord) (action : WG.M α)
    (keep : NativeKeeps records action) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  rw [liftWG_run] at run
  cases actual : (action.run before.wg).run before.ambient with
  | error e => simp only [actual,Except.map] at run; cases run
  | ok out =>
    rcases out with ⟨⟨x,g⟩,a⟩
    simp only [actual,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    rcases run with ⟨rfl,rfl⟩
    exact (hoare_iff_run _ _ _).mp (keep before.wg) before.ambient (x,g) a pre actual

end Leanux.Proofs.WG.Progress.RecordSuffix
