import Leanux.Proofs.WG.Lifetimes.HandshakeConsume

/-! The five complete Noise construction/consumption and MAC calls, retaining
their actual result types. These are local calls, not a handshake worker or an
assumption that scalar references designate their intended historical owner. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

inductive HandshakeCall where
  | createInitiation (pid : PeerId)
  | createResponse (pid : PeerId)
  | consumeInitiation (msg : List UInt8)
  | consumeResponse (msg : List UInt8)
  | addMac (pid : PeerId) (msg : List UInt8)

namespace HandshakeCall

def Result : HandshakeCall → Type
  | .createInitiation .. | .createResponse .. => Option (List UInt8)
  | .consumeInitiation .. | .consumeResponse .. => Option PeerId
  | .addMac .. => List UInt8

def original (call : HandshakeCall) : WG.M call.Result := match call with
  | .createInitiation pid => WG.createInitiation pid
  | .createResponse pid => WG.createResponse pid
  | .consumeInitiation msg => WG.consumeInitiation msg
  | .consumeResponse msg => WG.consumeResponse msg
  | .addMac pid msg => addMacToPacket pid msg

def observed (call : HandshakeCall) : MixedM call.Result := match call with
  | .createInitiation pid => createInitiationPrefix pid
  | .createResponse pid => createResponsePrefix pid
  | .consumeInitiation msg => consumeInitiationPrefix msg
  | .consumeResponse msg => consumeResponsePrefix msg
  | .addMac pid msg => addMacToPacketPrefix pid msg

theorem erases (call : HandshakeCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | createInitiation pid => exact createInitiationPrefix_erases pid
  | createResponse pid => exact createResponsePrefix_erases pid
  | consumeInitiation msg => exact consumeInitiationPrefix_erases msg
  | consumeResponse msg => exact consumeResponsePrefix_erases msg
  | addMac pid msg => exact addMacToPacketPrefix_erases pid msg

theorem preserves_ambient (c : AmbientContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (liftIndex (indexInsert owner))))
    (call : HandshakeCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | createInitiation pid => exact createInitiationPrefix_preserves c hi pid
  | createResponse pid => exact createResponsePrefix_preserves c hi pid
  | consumeInitiation msg => exact consumeInitiationPrefix_preserves c msg
  | consumeResponse msg => exact consumeResponsePrefix_preserves c msg
  | addMac pid msg => exact addMacToPacketPrefix_preserves c pid msg

theorem preserves_ambient_product (c : ProductAmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (liftIndex (indexInsert owner)))))
    (call : HandshakeCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | createInitiation pid => exact createInitiationPrefix_preserves_product c hi pid
  | createResponse pid => exact createResponsePrefix_preserves_product c hi pid
  | consumeInitiation msg => exact consumeInitiationPrefix_preserves_product c msg
  | consumeResponse msg => exact consumeResponsePrefix_preserves_product c msg
  | addMac pid msg => exact addMacToPacketPrefix_preserves_product c pid msg

theorem allocation (call : HandshakeCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed := by
  apply call.preserves_ambient allocationAmbient
  intro owner
  apply StatePrefixEnsures.lift _ (fun h w _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  have hp : Hoare (liftIndex (indexInsert owner)) (AllocationInv h)
      (fun _ => AllocationInv h) := by
    apply hoare_liftIndex
    intro g d table hg hd
    apply hg.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [hd]
    · simp [allocationMetadata, deviceAllocationMetadata, hd]
  exact (hoare_iff_run_ambient _ _ _).mp hp w ambient x v ambient' hi hr

end HandshakeCall

/-- The original MAC1 update has happened before an expiry-record Stop.
The premises name consecutive original operations, without a history premise. -/
theorem addMacToPacketPrefix_clock_failure (pid : PeerId) (msg : List UInt8)
    (w written clockEntry : WGWorld) (ambient writtenAmbient clockAmbient : Ambient)
    (p : Peer) (h : List LifetimeEvent) (e : Stop)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient))
    (hw : ((setPeer pid {p with lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)), haveSentMac1 := true}).run w).run ambient = .ok (((), written), writtenAmbient))
    (hb : ((branch .addMacCookieValid p.cookieIsValid : WG.M Bool).run written).run writtenAmbient = .ok ((true, clockEntry), clockAmbient))
    (hc : ((branchExpired .addMacCookieFresh p.cookieBirthdate COOKIE_FRESH_SECONDS (!·)).run clockEntry).run clockAmbient = .error e) :
    runStatePrefix (addMacToPacketPrefix pid msg) w ambient h =
      (.error e, h ++ [.peer (.read pid p.internalId), .peer (.write pid p.internalId)]) := by
  have present : w.dev.isSome = true := by
    cases hd : w.dev with
    | none =>
      simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hp
      cases hp
    | some d => rfl
  simp [addMacToPacketPrefix, andPrefix, runStatePrefix_bind, liftWGPrefix, runStatePrefix_lift,
    getPeerMixed_run, setPeerMixed_run, hp, hw, present, hb, hc, List.append_assoc]

end Leanux.Proofs.WG.Lifetimes
