import Leanux.Proofs.WG.Roaming.InitiationCallSource
import Leanux.Proofs.WG.Roaming.InitiationCallProductModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

def initiationPacketPrefix (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    Leanux.M (Option InitiationCallCut) := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.initiationPacketPrefix msg src underLoad)
  pure (out.map (restoreInitiationCallCut fixture))

def initiationAfterSetter (msg : List UInt8) (pid : PeerId) : Leanux.M Unit :=
  liftWG (Roaming.initiationAfterSetter msg pid)

def initiationCallSuffix (msg : List UInt8) (src : SkbSource) : Option InitiationCallCut → Leanux.M Unit
  | none => pure ()
  | some cut => liftWG (do
    setPeerEndpointFromSkb cut.consumed.pid src
    Roaming.initiationAfterSetter msg cut.consumed.pid)

def initiationCallPrefix (msg : List UInt8) (src : SkbSource) : Leanux.M (Option InitiationCallCut) := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.initiationCallPrefix msg src)
  pure (out.map (restoreInitiationCallCut fixture))

def observedInitiationHandshake (msg : List UInt8) (src : SkbSource) :
    Leanux.M (Campaign2.Product.Outcome (Option InitiationCallCut)) := do
  let observed ← Campaign2.Product.inspect (initiationCallPrefix msg src)
  liftWG (receiveHandshakePacket msg src)
  pure observed

theorem observedInitiationHandshake_erase (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observedInitiationHandshake msg src; pure ()) = liftWG (receiveHandshakePacket msg src) := by
  funext w
  change (((liftWG (receiveHandshakePacket msg src)).run w >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((initiationCallPrefix msg src).run w), out.2))
      >>= fun out => Except.ok ((), out.2)) = (liftWG (receiveHandshakePacket msg src)).run w
  cases run : (liftWG (receiveHandshakePacket msg src)).run w with
  | error e => rfl
  | ok pair => rcases pair with ⟨value, final⟩; cases value; rfl

theorem initiationPacket_source (msg : List UInt8) (src : SkbSource) (underLoad : Bool)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (initiationPacketPrefix msg src underLoad >>= initiationCallSuffix msg src) =
      liftWG (Index.receivePacketBody msg src underLoad) := by
  rw [← Roaming.initiationPacket_source msg src underLoad kind]
  funext w
  dsimp only [initiationPacketPrefix, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
  cases run : ((Roaming.initiationPacketPrefix msg src underLoad).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at run; rw [run]
  | ok pair =>
    rcases pair with ⟨⟨out, current⟩, after⟩
    simp only [StateT.run] at run
    rw [run]
    cases out <;> rfl

theorem receiveHandshakePacket_initiation (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (initiationCallPrefix msg src >>= initiationCallSuffix msg src) = liftWG (receiveHandshakePacket msg src) := by
  rw [← Roaming.receiveHandshakePacket_initiation msg src kind]
  funext w
  dsimp only [initiationCallPrefix, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
  cases run : ((Roaming.initiationCallPrefix msg src).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at run; rw [run]
  | ok pair =>
    rcases pair with ⟨⟨out, current⟩, after⟩
    simp only [StateT.run] at run
    rw [run]
    cases out <;> rfl

def initiationCallTranscript (msg : List UInt8) (src : SkbSource) :
    Leanux.M (Campaign2.Product.Outcome (Option InitiationCallCut)) := do
  let candidate ← initiationCallPrefix msg src
  let atCut ← Campaign2.Product.read
  initiationCallSuffix msg src candidate
  return .ok (candidate, atCut)

theorem observedInitiationHandshake_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    observedInitiationHandshake msg src = initiationCallTranscript msg src := by
  funext w
  change ((liftWG (receiveHandshakePacket msg src)).run w >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((initiationCallPrefix msg src).run w), out.2)) = _
  rw [← receiveHandshakePacket_initiation msg src kind]
  change (((initiationCallPrefix msg src).run w >>= fun out =>
    (initiationCallSuffix msg src out.1).run out.2) >>= fun out =>
      Except.ok (Campaign2.Product.observeResult ((initiationCallPrefix msg src).run w), out.2)) =
    ((initiationCallPrefix msg src).run w >>= fun cut =>
      (initiationCallSuffix msg src cut.1).run cut.2 >>= fun out =>
        Except.ok (Except.ok (cut.1, Campaign2.Product.snapshot cut.2), out.2))
  cases hp : (initiationCallPrefix msg src).run w with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    cases hs : (initiationCallSuffix msg src candidate).run atCut <;> rfl

end Leanux.Proofs.WG.Roaming.Product
