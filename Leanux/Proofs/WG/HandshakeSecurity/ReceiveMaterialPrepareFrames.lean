import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialPrepareSource
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialNativeWorkers

/-! Complete native decrypt preparation retains old allocation cores and the
numeric frontier while publishing only the selected packet's new certificate. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity PublicationHistory AuthenticatedEffects Responder
open Origins.Retaining
set_option maxHeartbeats 600000

theorem prepare_core : SameView pool RxWorkers.prepareSource := by
  intro initial
  unfold RxWorkers.prepareSource getRxSkb setRxSkb
  material_lower
  repeat' first
    | (index_material_head decryptPacket; exact (decrypt_core _).wp (fun p => p = initial))
    | (index_material_head RxWorkers.publishSource; exact (publish_core _ _).wp (fun p => p = initial))
    | (index_material_head modifyDev
       apply (pool_of_material (modifyDev_material _ ?_)).wp (fun p => p = initial)
       intro d; rfl)
    | core_traffic (fun p => p = initial)

theorem prepare_lower (bound : Nat) : Preserves (ResidentMaterial.Lower bound) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource getRxSkb setRxSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head decryptPacket; exact ResidentMaterial.NativeFrames.lower_decrypt _)
    | (allocation_release_head RxWorkers.publishSource; exact ResidentMaterial.NativeFrames.lower_slot_fields (CurrentSlots.publish_fields _ _))
    | (allocation_release_head liftSkb; exact ResidentMaterial.lower_frame ((ResidentMaterial.skb_allocation_view _).factor (fun fields => fields.2.1)))
    | (allocation_release_head getDev; exact ResidentMaterial.lower_frame (getDev_sameWGStore.of_factor
        (fun s : WGStoreView => ResidentMaterial.cursor {dev := s.dev}) _ (fun _ => rfl)))
    | (allocation_release_head modifyDev
       apply ResidentMaterial.lower_frame
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w a result v b run
       cases run
       simp only [ResidentMaterial.cursor,Option.map_map,Function.comp_def])
    | material_cursor_step

/-- The actual selected-source receipt establishes the new crypted binding;
every other crypted packet retains its old certificate and allocation core. -/
theorem prepare_normal (w v : WGWorld) (a b : Ambient)
    (h t : List TransportDriver.OriginEvent) (value : Option PeerId)
    (hi : Inv h w) (bounded : KeyBounds w)
    (run : runWGPrefix RxOrigin.prepare w a h = (.ok ((value,v),b),t)) : Inv t v := by
  cases value with
  | none =>
    obtain ⟨rfl,rfl⟩ := native_prepare_none w v a b h t run
    exact hi
  | some pid =>
    have native : ((RxWorkers.prepareSource).run w).run a = .ok ((some pid,v),b) :=
      (RxOrigin.prepare_erases w a h).symm.trans (congrArg Prod.fst run)
    have cores := (ProjectedAction.iff_run_ambient _ _ _).mp prepare_core w a (some pid) v b native
    obtain ⟨selected,r,pre,tail,valid,position,frame,dead,published⟩ :=
      prepare_selected_bound w v a b h t pid bounded run
    intro after device id pkt cell crypted
    have stored : (RxDisposition.nativeRxStore v).2 id = some pkt := by
      simp only [RxDisposition.nativeRxStore,device,Option.bind_some,cell]
    by_cases same : id = selected
    · subst id
      cases output : r.value.2 with
      | none =>
        obtain ⟨final,hfinal,hdead⟩ := dead output
        have packet : pkt = final := Option.some.inj (stored.symm.trans hfinal)
        subst pkt
        cases crypted.symm.trans hdead
      | some out =>
        obtain ⟨pub,bound⟩ := published out output
        obtain ⟨resident,stamp⟩ := TransportPublication.published_packet selected r out pid v b pub
        have packet : pkt = {out with state := .crypted} := Option.some.inj (stored.symm.trans resident)
        subst pkt
        have below := publication_below selected r out pid v b pub bound after device
        obtain ⟨core,certificate,conditional⟩ := publication_certificate selected r out pid v b pub (h ++ pre) tail
        rw [position]
        exact ⟨below,core,certificate,conditional⟩
    · have packet := congrFun (congrArg (fun s => s.2.1) frame) id
      have old : (RxDisposition.nativeRxStore w).2 id = some pkt := by
        simpa only [around,same,ite_false,stored] using packet.symm
      obtain ⟨prior,priorDevice,priorStored⟩ := Option.bind_eq_some_iff.mp old
      obtain ⟨bound,core,certificate,conditional⟩ := hi prior priorDevice id pkt priorStored crypted
      have stamp : packetStamp v id = packetStamp w id :=
        congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst frame)
      have low : ResidentMaterial.Lower prior.nextKeypairId w := by
        intro frontier found
        have equal : frontier = prior.nextKeypairId := by
          simpa only [ResidentMaterial.cursor,priorDevice,Option.map_some,Option.some.injEq] using found.symm
        omega
      have finalBound := (hoare_iff_run_ambient _ _ _).mp (prepare_lower prior.nextKeypairId)
        w a (some pid) v b low native after.nextKeypairId (by simp [ResidentMaterial.cursor,device])
      rw [position,List.append_assoc]
      exact ⟨Nat.lt_of_lt_of_le bound finalBound,core,
        (certificate.transport stamp).append (pre ++ .receipt (.decrypt selected r) :: tail),
        fun current resident => conditional current (by simpa only [cores] using resident)⟩

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
