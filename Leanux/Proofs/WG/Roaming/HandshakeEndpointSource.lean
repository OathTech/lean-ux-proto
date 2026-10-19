import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Index.ReceiveOperations
import Leanux.Proofs.WG.Origins.HandshakeSources
import Leanux.Proofs.Logged.PrefixState

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeEndpoint
open Leanux Leanux.WG Leanux.Proofs.Logged Std.Do Origins
structure Lift (m : Type → Type) [Monad m] where
  action : {α : Type} → WG.M α → m α
  bind : ∀ {α β : Type} (a : WG.M α) (f : α → WG.M β),
    action (a >>= f) = (action a >>= fun x => action (f x))
  pure : ∀ {α : Type} (x : α), action (pure x) = pure x
  read_ignore : ∀ {α : Type} (a : m α), (action Campaign2.read >>= fun _ => a) = a
  abort : ∀ {α β : Type} (message : String) (next : α → m β),
    (action (invariant message) >>= next) = action (invariant message : WG.M β)
variable {m : Type → Type} [Monad m] (L : Lift m)
variable {α β : Type}
theorem lift_bind (a : WG.M α) (f : α → WG.M β) :
    L.action (a >>= f) = (L.action a >>= fun x => L.action (f x)) := L.bind a f
theorem lift_pure (x : α) : L.action (pure x) = pure x := L.pure x
theorem read_ignore (a : m α) : (L.action Campaign2.read >>= fun _ => a) = a := L.read_ignore a
def ops (endpoint : PeerId → SkbSource → m Unit) :
    HandshakeSources.Ops (m) where
  step := L.action
  session := fun pid => L.action (beginSession pid)
  modifyPeer := fun pid f => L.action (do setPeer pid (f (← getPeer pid)))
  create := fun pid => L.action (createResponse pid)
  mac := fun pid msg => L.action (addMacToPacket pid msg)
  send := fun pid msg => L.action (sendBufferToPeer pid msg)
  derived := fun pid => L.action (timersSessionDerived pid)
  traversal := fun pid => L.action (timersTraversal pid)
  sent := fun pid => L.action (timersAnyAuthenticatedPacketSent pid)
  cookie := fun msg src => L.action (sendHandshakeCookie msg src)
  initiation := fun msg => L.action (consumeInitiation msg)
  response := fun msg => L.action (consumeResponse msg)
  endpoint := endpoint
  complete := fun pid => L.action (timersHandshakeComplete pid)
  keepalive := fun pid => L.action (sendKeepalive pid)
  received := fun pid => L.action (timersAnyAuthenticatedPacketReceived pid)
  put := fun peer => L.action (peerPut peer)
  cookieConsume := fun msg => L.action (cookieMessageConsume msg)
theorem ops_step (endpoint : PeerId → SkbSource → m Unit) {α : Type} (a : WG.M α) :
    (ops L endpoint).step a = L.action a := rfl
theorem ops_initiation (endpoint : PeerId → SkbSource → m Unit) (msg : List UInt8) :
    (ops L endpoint).initiation msg = L.action (consumeInitiation msg) := rfl
theorem ops_response (endpoint : PeerId → SkbSource → m Unit) (msg : List UInt8) :
    (ops L endpoint).response msg = L.action (consumeResponse msg) := rfl
theorem ops_endpoint (endpoint : PeerId → SkbSource → m Unit) (pid : PeerId) (src : SkbSource) :
    (ops L endpoint).endpoint pid src = endpoint pid src := rfl
theorem ops_cookie (endpoint : PeerId → SkbSource → m Unit) (msg : List UInt8) (src : SkbSource) :
    (ops L endpoint).cookie msg src = L.action (sendHandshakeCookie msg src) := rfl
theorem ops_session (endpoint : PeerId → SkbSource → m Unit) (pid : PeerId) :
    (ops L endpoint).session pid = L.action (beginSession pid) := rfl
theorem ops_derived (endpoint : PeerId → SkbSource → m Unit) (pid : PeerId) :
    (ops L endpoint).derived pid = L.action (timersSessionDerived pid) := rfl
theorem ops_complete (endpoint : PeerId → SkbSource → m Unit) (pid : PeerId) :
    (ops L endpoint).complete pid = L.action (timersHandshakeComplete pid) := rfl
theorem ops_keepalive (endpoint : PeerId → SkbSource → m Unit) (pid : PeerId) :
    (ops L endpoint).keepalive pid = L.action (sendKeepalive pid) := rfl
theorem ops_modifyPeer (endpoint : PeerId → SkbSource → m Unit) (pid : PeerId) (f : Peer → Peer) :
    (ops L endpoint).modifyPeer pid f = L.action (do setPeer pid (f (← getPeer pid))) := rfl
theorem ops_received (endpoint : PeerId → SkbSource → m Unit) (pid : PeerId) :
    (ops L endpoint).received pid = L.action (timersAnyAuthenticatedPacketReceived pid) := rfl
theorem ops_traversal (endpoint : PeerId → SkbSource → m Unit) (pid : PeerId) :
    (ops L endpoint).traversal pid = L.action (timersTraversal pid) := rfl
theorem ops_put (endpoint : PeerId → SkbSource → m Unit) (pid : Option PeerId) :
    (ops L endpoint).put pid = L.action (peerPut pid) := rfl
theorem response_source [LawfulMonad m] (endpoint : PeerId → SkbSource → m Unit) (pid : PeerId) :
    HandshakeSources.responseWith (ops L endpoint) pid =
      L.action (sendHandshakeResponse pid) := by
  simp only [HandshakeSources.responseWith, ops, sendHandshakeResponse, lift_bind, lift_pure,
    bind_assoc, apply_ite]
  congr 1
  funext now
  congr 1
  funext p
  congr 1
  funext ignored
  congr 1
  funext created
  cases created <;> simp only [lift_bind, lift_pure, apply_ite]
theorem bind_congr_right (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
theorem bind_if (condition : Prop) [Decidable condition]
    (yes no : m α) (next : α → m β) :
    ((if condition then yes else no) >>= next) =
      if condition then yes >>= next else no >>= next := by split <;> rfl
theorem abort_bind (message : String) (next : α → m β) :
    (L.action (invariant message) >>= next) =
      L.action (invariant message : WG.M β) := L.abort message next
theorem branch_native (decision : Decision) (value : Bool) :
    (branch decision value : WG.M Bool) = (do
      (monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
        decision, outcome := value, netRx := a.netRxSection}} : AmbientM Unit) : WG.M Unit)
      pure value) := rfl

def native : Lift WG.M where
  action := fun a => a
  bind := fun _ _ => rfl
  pure := fun _ => rfl
  read_ignore := fun _ => rfl
  abort := fun _ _ => rfl

def prefixLift {E : Type} : Lift (WGPrefix E) where
  action := liftWGPrefix
  bind := by
    intro α β action next
    funext g ambient history
    change runStatePrefix (liftWGPrefix (action >>= next)) g ambient history =
      runStatePrefix (liftWGPrefix action >>= fun x => liftWGPrefix (next x)) g ambient history
    rw [runStatePrefix_bind]
    simp only [liftWGPrefix, runStatePrefix_lift]
    change ((action.run g).run ambient >>= fun ((x,g'),a') => ((next x).run g').run a', history) = _
    cases result : (action.run g).run ambient with
    | error e => rfl
    | ok value => rcases value with ⟨⟨x,g'⟩,a'⟩; rfl
  pure := fun _ => rfl
  read_ignore := fun _ => rfl
  abort := fun _ _ => rfl

theorem packet_original (msg : List UInt8) (src : SkbSource) (loaded : Bool) :
    Index.receivePacketBody msg src loaded =
      (cookieValidatePacket msg src loaded >>= fun mac => Cookies.afterMac msg src loaded mac) := by
  unfold Index.receivePacketBody
  apply congrArg (fun f => cookieValidatePacket msg src loaded >>= f)
  funext mac
  rfl

end Leanux.Proofs.WG.Roaming.HandshakeEndpoint
