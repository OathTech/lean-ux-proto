import Leanux.Proofs.WG.Progress.NativeSuffixSource

/-! Actual reference release and responder confirmation retain the recorded suffix. Missing owners, invalid reference counts, queued releases and timer-release failures retain their original Stops. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem native_modifyAmbient (records : List HiddenRecord) (f : Ambient → Ambient)
    (same : ∀ a, (f a).hidden = a.hidden) :
    NativeKeeps records (modifyAmbient f : WG.M Unit) := by
  apply native_ambient
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  cases run
  simpa only [same] using pre

theorem native_liftIndex {α : Type} (records : List HiddenRecord) (action : IndexM α)
    (keep : ∀ s, Preserves (fun a=>Tail records a.hidden) (action.run s)) :
    NativeKeeps records (liftIndex action) := by
  unfold liftIndex
  apply native_bind records _ _ (native_getDev records)
  intro d
  apply native_bind records _ _ (native_ambient records _ (keep _))
  intro out
  exact native_bind records _ _ (native_modifyDev records _) (fun _=>native_pure records _)

theorem native_indexRemove (records : List HiddenRecord) (owner : IndexOwner) :
    NativeKeeps records (indexRemove owner : WG.M Unit) := by
  apply native_liftIndex
  intro table
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  cases run
  exact pre

theorem native_refcountDec (records : List HiddenRecord) (count : Nat) :
    NativeKeeps records (refcountDecAndTest count : WG.M Bool) := by
  unfold refcountDecAndTest
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_branchCmp records _ _ _ _
    | with_reducible exact native_unsupported records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem native_retirePeer (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (retirePeerUnits pid) := by
  unfold retirePeerUnits
  exact native_bind records _ _ (native_modifyAmbient records _ (fun _=>rfl))
    (fun _=>native_modify records _)

theorem peerPut_retains (records : List HiddenRecord) (peer : Option PeerId) :
    NativeKeeps records (peerPut peer) := by
  unfold peerPut requireNotPending
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_getPeer records _
    | with_reducible exact native_setPeer records _ _
    | with_reducible exact native_refcountDec records _
    | with_reducible exact native_indexRemove records _
    | with_reducible exact native_modifyDev records _
    | with_reducible exact native_retirePeer records _
    | with_reducible exact native_invariant records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem keypairPut_retains (records : List HiddenRecord) (key : Option KeypairId) (now : Bool) :
    NativeKeeps records (keypairPut key now) := by
  unfold keypairPut
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_getKeypair records _
    | with_reducible exact native_setKeypair records _ _
    | with_reducible exact native_refcountDec records _
    | with_reducible exact native_indexRemove records _
    | with_reducible exact native_peerDeref records _
    | with_reducible exact native_modifyDev records _
    | with_reducible exact native_invariant records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem native_peerUpdate (records : List HiddenRecord) (pid : PeerId) (f : Peer → Peer) :
    NativeKeeps records (do setPeer pid (f (←getPeer pid))) :=
  native_bind records _ _ (native_getPeer records pid) (fun _=>native_setPeer records _ _)

theorem native_modifyPeer (records : List HiddenRecord) (pid : PeerId) (f : Peer → Peer) :
    NativeKeeps records ((noise_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := native_peerUpdate records pid f

theorem confirmation_retains (records : List HiddenRecord) (pid : PeerId) (kid : KeypairId) :
    NativeKeeps records (receivedWithKeypair pid kid) := by
  unfold receivedWithKeypair
  repeat' first
    | with_reducible exact native_getPeer records _
    | with_reducible exact native_modifyPeer records _ _
    | with_reducible exact native_branch records _ _
    | with_reducible exact keypairPut_retains records _ _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Progress.RecordSuffix
