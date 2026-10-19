import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialPublication

/-! The actual ring-selected decrypt entry retains the native resident-key
frontier. This adds the missing entry fact to the C1 source decomposition,
without connecting two journals through endpoint erasure. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity PublicationHistory AuthenticatedEffects Responder

/-- Numeric key bounds required only at actual resident keys. They are distinct
from peer-slot bounds and from the global allocation-stamp frontier. -/
def KeyBounds (w : WGWorld) : Prop :=
  ∀ d, w.dev = some d → ∀ slot key, d.keypairs[slot]? = some key → slot < d.nextKeypairId

theorem prepare_selected_bound (w v : WGWorld) (a b : Ambient)
    (h t : List TransportDriver.OriginEvent) (pid : PeerId) (bounded : KeyBounds w)
    (run : runWGPrefix RxOrigin.prepare w a h = (.ok ((some pid,v),b),t)) :
    ∃ id, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ pre tail,
      r.Valid (RxOrigin.readDecrypt id) ∧
      t = h ++ pre ++ .receipt (.decrypt id r) :: tail ∧
      around id v = around id w ∧
      (r.value.2 = none → ∃ pkt, (RxDisposition.nativeRxStore v).2 id = some pkt ∧ pkt.state = .dead) ∧
      (∀ out, r.value.2 = some out → Published id r out pid v b ∧
        ∀ d, r.before.dev = some d → r.value.1.keypair < d.nextKeypairId) := by
  obtain ⟨d,id,ring,hd,queue,selectedRun⟩ := prepare_selected w v a b h t pid run
  obtain ⟨r,before,tail,entry,ambientEntry,valid,read,finishRun,position,published⟩ :=
    selected_receipt id _ v _ b h t pid selectedRun
  obtain ⟨pre,hprefix⟩ := StateAppends.focus MaterialOrigin.Event.life MaterialOrigin.life?
    (RxOrigin.readDecryptPrefix id) (Packets.update w (fun d => {d with decryptQueue := ring}))
      (CounterWindow.record a .decWorkerConsumed true) h
  change (runWGPrefix (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id))
    _ _ h).2 = h ++ pre at hprefix
  rw [read] at hprefix
  change before = h ++ pre at hprefix
  have finishSource := (finish_erases id r.value r.after r.ambientAfter _).symm.trans (congrArg Prod.fst finishRun)
  have decryptFrame := readDecrypt_views id r.before r.after r.ambientBefore r.ambientAfter r.value valid
  have finalFrame := (ProjectedAction.iff_run_ambient _ _ _).mp (finish_around id r.value)
    r.after r.ambientAfter pid v b finishSource
  have initialFrame : around id r.before = around id w := by
    rw [entry]
    simp only [around,RxDisposition.nativeRxStore,CurrentIdentity.peerView,Packets.update,
      Option.map_map,Option.bind_map,Function.comp_def]
  have wholeFrame : around id r.after = around id r.before := by
    simp only [around,decryptFrame.1,decryptFrame.2]
  refine ⟨id,r,pre,tail,valid,?_,finalFrame.trans (wholeFrame.trans initialFrame),?_,?_⟩
  · simpa only [hprefix,List.append_assoc,List.singleton_append] using position
  · intro noneResult
    have shape : r.value = (r.value.1,none) := Prod.ext rfl noneResult
    rw [shape] at finishSource
    exact finish_none_dead id r.value.1 r.after v r.ambientAfter b pid finishSource
  · intro out output
    refine ⟨published out output,?_⟩
    obtain ⟨prior,key,device,packet,keyStored,rest⟩ := RxOrigin.decrypt_receipt id r out valid output
    have actual : prior = {d with decryptQueue := ring} := by
      apply Option.some.inj
      rw [←device,entry]
      simp only [Packets.update,hd,Option.map_some]
    subst prior
    intro current currentDevice
    have same := Option.some.inj (device.symm.trans currentDevice)
    subst current
    exact bounded d hd r.value.1.keypair key keyStored

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
