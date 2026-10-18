import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteFrames
import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteEffects
import Leanux.Proofs.WG.Roaming.HandshakeRemoteWholeClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ReceiveStepRemote
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Noise Lifetimes Queues Std.Do

theorem native_empty (g : WGWorld) (ambient : Ambient) (d : Device)
    (ring : PtrRing (List UInt8 × SkbSource)) (device : g.dev = some d)
    (selected : d.handshakeQueue.consume = (none,ring)) :
    ((receiveStep.run g).run ambient) =
      .ok ((false,g),Noise.ReceiveStepCaller.pollAmbient ambient false) := by
  rw [← Noise.ReceiveStepCaller.observeStep_discard]
  change (Noise.ReceiveStepCaller.observeStep g ambient >>= _) = _
  rw [Noise.ReceiveStepCaller.observeStep_empty_run g ambient d ring device selected]
  rfl

theorem native_selected (g : WGWorld) (ambient : Ambient) (d : Device)
    (msg : List UInt8) (src : SkbSource) (ring : PtrRing (List UInt8 × SkbSource))
    (device : g.dev = some d)
    (selected : d.handshakeQueue.consume = (some (msg,src),ring)) :
    ((receiveStep.run g).run ambient) =
      (((receiveHandshakePacket msg src).run
        (Noise.ReceiveStepCaller.dequeueWorld g ring)).run
        (Noise.ReceiveStepCaller.pollAmbient ambient true)).map
        (fun ((_,current),after) => ((true,Noise.ReceiveStepCaller.decrementWorld current),after)) := by
  rw [← Noise.ReceiveStepCaller.observeStep_discard]
  change (Noise.ReceiveStepCaller.observeStep g ambient >>= _) = _
  rw [Noise.ReceiveStepCaller.observeStep_consumed_run g ambient d msg src ring device selected]
  rw [← Noise.ReceptionCaller.observeClassified_discard msg src]
  change ((Noise.ReceptionCaller.observeClassified msg src
      (Noise.ReceiveStepCaller.dequeueWorld g ring)
      (Noise.ReceiveStepCaller.pollAmbient ambient true)).map _ >>= _) = _
  dsimp only [StateT.run,StateT.bind,StateT.pure,Bind.bind,Pure.pure]
  cases Noise.ReceptionCaller.observeClassified msg src
      (Noise.ReceiveStepCaller.dequeueWorld g ring)
      (Noise.ReceiveStepCaller.pollAmbient ambient true) with
  | error stop => rfl
  | ok pair =>
    obtain ⟨⟨call,current⟩,after⟩ := pair
    rfl

theorem empty_run (w : World) (d : Device) (ring : PtrRing (List UInt8 × SkbSource))
    (device : w.wg.dev = some d) (selected : d.handshakeQueue.consume = (none,ring)) :
    (liftWG receiveStep).run w = .ok (false,emptyReturn w) := by
  rw [liftWG_run,native_empty w.wg w.ambient d ring device selected]
  rfl

theorem selected_run (w : World) (d : Device)
    (msg : List UInt8) (src : SkbSource) (ring : PtrRing (List UInt8 × SkbSource))
    (device : w.wg.dev = some d)
    (selected : d.handshakeQueue.consume = (some (msg,src),ring)) :
    (liftWG receiveStep).run w =
      ((liftWG (receiveHandshakePacket msg src)).run (dequeued w ring)).map
        (fun (_,current) => (true,decremented current)) := by
  rw [liftWG_run,native_selected w.wg w.ambient d msg src ring device selected,liftWG_run]
  dsimp only [dequeued]
  cases (((receiveHandshakePacket msg src).run
      (Noise.ReceiveStepCaller.dequeueWorld w.wg ring)).run
      (Noise.ReceiveStepCaller.pollAmbient w.ambient true)) with
  | error stop => rfl
  | ok pair =>
    obtain ⟨⟨value,current⟩,after⟩ := pair
    cases value
    rfl

theorem handshake_receipt (msg : List UInt8) (src : SkbSource) (w v : World)
    (run : (liftWG (receiveHandshakePacket msg src)).run w = .ok ((),v)) :
    ∃ receipt,
      (Product.observedHandshakeRemotes msg src).run w = .ok (receipt,v) ∧
      Product.HandshakeFinalRemotes msg src (Campaign2.Product.snapshot w)
        receipt (Campaign2.Product.snapshot v) := by
  rw [← Product.observedHandshakeRemotes_erase msg src] at run
  change ((Product.observedHandshakeRemotes msg src).run w >>= fun (_,current) =>
    .ok ((),current)) = _ at run
  cases observed : (Product.observedHandshakeRemotes msg src).run w with
  | error stop => rw [observed] at run; cases run
  | ok pair =>
    obtain ⟨receipt,current⟩ := pair
    rw [observed] at run
    cases run
    exact ⟨receipt,rfl,
      Product.observedHandshakeRemotes_facts msg src (Campaign2.Product.snapshot w)
        w receipt v rfl observed⟩

theorem complete (r : RunWitness Bool) (valid : r.Valid (liftWG receiveStep)) :
    ∃ q : Observation, Matches r q ∧ q.Facts := by
  obtain ⟨value,w,v⟩ := r
  change (liftWG receiveStep).run w = .ok (value,v) at valid
  cases device : w.wg.dev with
  | none =>
    have read : ((getDev.run w.wg).run w.ambient) =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      simp [getDev,device,invariant,AmbientM.invariant]
      rfl
    have stopped : ((receiveStep.run w.wg).run w.ambient) =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      change (((getDev.run w.wg).run w.ambient) >>= _) = _
      rw [read]
      rfl
    rw [liftWG_run,stopped] at valid
    cases valid
  | some d =>
    cases selected : d.handshakeQueue.consume with
    | mk packet ring =>
      cases packet with
      | none =>
        rw [empty_run w d ring device selected] at valid
        cases valid
        refine ⟨⟨Campaign2.Product.snapshot w,Campaign2.Product.snapshot (emptyReturn w),
          false,none⟩,?_,?_⟩
        · exact ⟨rfl,rfl,rfl,d,ring,device,selected,rfl,rfl⟩
        · exact ⟨d,device,rfl,congrArg Prod.fst selected,rfl⟩
      | some packet =>
        obtain ⟨msg,src⟩ := packet
        rw [selected_run w d msg src ring device selected] at valid
        cases received : (liftWG (receiveHandshakePacket msg src)).run (dequeued w ring) with
        | error stop => rw [received] at valid; cases valid
        | ok pair =>
          obtain ⟨returned,callFinish⟩ := pair
          cases returned
          rw [received] at valid
          cases valid
          obtain ⟨receipt,observed,facts⟩ := handshake_receipt msg src (dequeued w ring) callFinish received
          let call : Call := ⟨msg,src,Campaign2.Product.snapshot (dequeued w ring),
            Campaign2.Product.snapshot callFinish,receipt⟩
          refine ⟨⟨Campaign2.Product.snapshot w,
            Campaign2.Product.snapshot (decremented callFinish),true,some call⟩,?_,?_⟩
          · exact ⟨rfl,rfl,rfl,d,ring,device,selected,rfl,callFinish,observed,rfl,rfl,rfl⟩
          · exact ⟨d,device,rfl,congrArg Prod.fst selected,dequeue_remotes w ring,
              decrement_remotes callFinish,facts⟩

theorem run_origin (r : RunWitness Bool) (valid : r.Valid (liftWG receiveStep))
    (pid : PeerId) (remote : Nat × Nat × Nat × Nat)
    (present : remoteMap (Campaign2.Product.snapshot r.after).toSnapshot pid = some remote) :
    remoteMap (Campaign2.Product.snapshot r.before).toSnapshot pid = some remote ∨
      ∃ q : Observation, Matches r q ∧ q.Cause pid remote := by
  obtain ⟨q,matched,facts⟩ := complete r valid
  have final : remoteMap q.finish.toSnapshot pid = some remote := by
    rw [matched.2.1]
    exact present
  cases observation_origin q facts pid remote final with
  | inl old =>
    left
    simpa only [matched.1] using old
  | inr cause => exact Or.inr ⟨q,matched,cause⟩

end Leanux.Proofs.WG.Roaming.ReceiveStepRemote
