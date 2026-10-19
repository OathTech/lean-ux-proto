import Leanux.Proofs.WG.RetirementSecurity.HolderShutdownFrames

/-! Whole native shutdown carries the physical key account through actual
slot clearing, timer/work drains and socket retirement. Pending receive/TX
references remain funded; shutdown is not claimed to erase them immediately. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderShutdown
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders
set_option pp.structureInstances false

theorem purge (pid : PeerId) :
    Preserves (HolderDrain.Ready original carriers loans temporary) (purgeStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  unfold purgeStagedPackets at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,getter,run⟩ := run
  obtain ⟨same,time,d,hd,hp⟩ := getPeer_normal pid w read p a ar getter
  subst read
  subst ar
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,stats,as_,write,run⟩ := run
  cases write
  have changed : HolderEncrypt.fields
      {w with dev := w.dev.map fun d => {d with txDropped := d.txDropped+p.staged.length}} = HolderEncrypt.fields w := by
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    simp [hd,rxView]
  have points : ownershipPointView
      {w with dev := w.dev.map fun d => {d with txDropped := d.txDropped+p.staged.length}} = ownershipPointView w := by
    unfold ownershipPointView RetirementSecurity.keyReferenceView RetirementSecurity.keyAt ownershipAt peerAt packetKeyWords
    simp [hd]
  have kept := fields before changed points
  apply (hoare_iff_run_ambient _ _ _).mp
    (update pid (fun p => {p with staged := []}) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl) (fun _ => rfl))
    _ a result v b kept
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨p,_,a,by simp [getPeer,getDev,hd,hp],run⟩

theorem socket (new4 new6 : Option Nat) :
    Preserves (HolderDrain.Ready original carriers loans temporary) (socketReinit new4 new6) := by
  apply frame
  · apply (socketReinit_sameSocket new4 new6).of_factor
      (fun s : WGOwnedView => HolderEncrypt.fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8})
    intro w
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    simp only [socketView,socketDevice,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def]
    simp only [rxView,Option.map_map,Option.bind_map,Function.comp_def]
    rfl
  · apply (socketReinit_sameSocket new4 new6).of_factor
      (fun s : WGOwnedView => ownershipPointView {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8})
    intro w
    unfold ownershipPointView RetirementSecurity.keyReferenceView RetirementSecurity.keyAt ownershipAt peerAt packetKeyWords
    simp only [socketView,socketDevice,wgOwnedView,wgStoreView,Option.bind_map,
      Function.comp_def,Option.isSome_map]

/-- The actual stop loop clears each selected peer and executes its actual
work drains, preserving exact references for every remaining physical holder. -/
theorem stop : Preserves (HolderDrain.Ready original carriers loans temporary) wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [requireNotPending,branch,unsupported]
  repeat' first
    | (rx_retention_head getDev; exact read)
    | (rx_retention_head purgeStagedPackets; exact purge _)
    | (rx_retention_head timersStop; exact HolderDrain.timers_stop _)
    | (rx_retention_head handshakeClear; exact handshake _)
    | (rx_retention_head keypairsClear; exact HolderDrain.keys_clear _)
    | (rx_retention_head resetLastSentHandshake; exact reset _)
    | (rx_retention_head socketReinit; exact socket _ _)
    | (rx_retention_head modifyDev
       apply modify
       · intro w
         unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
         unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
         cases hd : w.dev <;> simp [hd,rxView]
       · intro w
         unfold ownershipPointView RetirementSecurity.keyReferenceView RetirementSecurity.keyAt ownershipAt peerAt packetKeyWords
         cases w.dev <;> simp)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (HolderDrain.Ready original carriers loans temporary)
       intro x u
       change Preserves (HolderDrain.Ready original carriers loans temporary) _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem down : Preserves (HolderDrain.Ready original carriers loans temporary) wgDown := by
  unfold wgDown
  apply preserves_bind
  · apply modify
    · intro w
      unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
      unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
      cases hd : w.dev <;> simp [hd,rxView]
    · intro w
      unfold ownershipPointView RetirementSecurity.keyReferenceView RetirementSecurity.keyAt ownershipAt peerAt packetKeyWords
      cases w.dev <;> simp
  · intro _; exact stop

end Leanux.Proofs.WG.RetirementSecurity.HolderShutdown
