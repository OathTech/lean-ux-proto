import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitReceipt

/-! Fixed front decision prefixes stop before the first counted effect.
The residual actions are the original release/error or overflow/splice paths;
no ledger or native result is introduced by this source factor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal CompleteCarrier Lifetimes Packets
set_option maxHeartbeats 600000

inductive Choice where
  | unreachable
  | refuse (code : Int)
  | release (peer : Option PeerId) (code : Int)
  | splice (pid : PeerId) (packets : List Packet)

/-- Exactly the selection guards and packet walk before disposal or splice. -/
def chooseWith [Monad m] (step : {α : Type} → WG.M α → m α)
    (input : Input) (peer : Option PeerId) : m Choice := do
  if ← step (branch .xmitNoPeer peer.isNone) then
    if !(← step (branch .xmitNoPeerInet (input.family == 4))) then
      _ ← step (branch .xmitNoPeerInet6 (input.family == 6))
    return .refuse (-ENOKEY)
  let some pid := peer | pure .unreachable
  let epFamily := (← step (getPeer pid)).endpoint.map (·.family) |>.getD 0
  if ← step (WG.andM (branch .xmitEndpointNotInet (epFamily != AF_INET))
      (branch .xmitEndpointNotInet6 (epFamily != AF_INET6))) then
    return .release peer (-EDESTADDRREQ)
  _ ← step (branch .xmitValidDst true)
  if !(← step (branch .xmitNotGso (input.packets.length < 2))) then
    if ← step (branch .xmitGsoError !(← step (envOk .skbSegment))) then
      return .release peer (-ENOMEM)
  let packets ← step (txWalk input.packets input.mtu [])
  _ ← step (branch .xmitWalk false)
  pure (.splice pid packets)

def selectedWith [Monad m] (o : HandshakeSecurity.StagedConservation.Front.Ops m)
    (input : Input) : Choice → m (Except Int (PeerId × List Packet))
  | .unreachable => o.step (invariant "unreachable")
  | .refuse code => do
    pure (.error (← o.step (txError input.family (input.packets.head?.getD {bytes := []}) code)))
  | .release peer code => do
    o.put peer
    pure (.error (← o.step (txError input.family (input.packets.head?.getD {bytes := []}) code)))
  | .splice pid packets => do o.trim pid; pure (.ok (pid,packets))

theorem choose_factor [Monad m] [LawfulMonad m]
    (o : HandshakeSecurity.StagedConservation.Front.Ops m) (input : Input) (peer : Option PeerId) :
    HandshakeSecurity.StagedConservation.Front.selectWith o input.family input.packets input.mtu peer =
      (chooseWith o.step input peer >>= selectedWith o input) := by
  unfold chooseWith HandshakeSecurity.StagedConservation.Front.selectWith
  simp only [bind_assoc]
  congr 1
  funext missing
  cases missing <;> simp only [Bool.false_eq_true,ite_false,ite_true,bind_assoc]
  · cases peer with
    | none => simp only [pure_bind,selectedWith]
    | some pid =>
      dsimp only
      simp only [bind_assoc]
      congr 1
      funext resident
      congr 1
      funext invalid
      cases invalid <;> simp only [Bool.false_eq_true,ite_false,ite_true,pure_bind,selectedWith,bind_assoc]
      congr 1
      funext destination
      congr 1
      funext small
      cases small <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,bind_assoc]
      · congr 1
        funext segment
        congr 1
        funext failed
        cases failed <;> simp only [Bool.false_eq_true,ite_false,ite_true,pure_bind,selectedWith,bind_assoc]
      · congr 1
        funext packets
        congr 1
        funext walked
        simp only [pure_bind,selectedWith]
  · congr 1
    funext inet
    cases inet <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,bind_assoc,pure_bind,selectedWith]

abbrev choose (input : Input) (peer : Option PeerId) : WGPrefix Event Choice :=
  chooseWith liftWGPrefix input peer

def afterSelected : Except Int (PeerId × List Packet) → WGPrefix Event (Except Int PeerId)
  | .error err => pure (.error err)
  | .ok (pid,packets) => do liftWGPrefix (xmitSplice pid packets); pure (.ok pid)

def resolve (input : Input) (choice : Choice) : WGPrefix Event (Except Int PeerId) :=
  selectedWith StagedAdmission.Front.ops input choice >>= afterSelected

def selection (input : Input) (peer : Option PeerId) : WGPrefix Event (Except Int PeerId) :=
  HandshakeSecurity.StagedConservation.Front.selectWith StagedAdmission.Front.ops
    input.family input.packets input.mtu peer >>= afterSelected

theorem selection_factor (input : Input) (peer : Option PeerId) :
    selection input peer = (choose input peer >>= resolve input) := by
  unfold selection
  rw [choose_factor]
  exact bind_assoc _ _ _

/-- The original front entry prefix, including the actual protocol check and
route lookup, before any counted disposal. -/
def decisionPrefix (input : Input) : WGPrefix Event (Except Int Choice) := do
  if !(← liftWGPrefix (txCheck input.family input.address input.packets input.mtu)) then
    return .error (-EPROTONOSUPPORT)
  let peer ← liftWGPrefix (lookupDst input.family input.address)
  pure (.ok (← choose input peer))

def suffix (input : Input) : Except Int Choice → WGPrefix Event (Except Int PeerId)
  | .error err => pure (.error err)
  | .ok decision => resolve input decision

theorem body_factor (input : Input) : body input = (decisionPrefix input >>= suffix input) := by
  change (do
    if !(← liftWGPrefix (txCheck input.family input.address input.packets input.mtu)) then
      return (Except.error (-EPROTONOSUPPORT) : Except Int PeerId)
    let peer ← liftWGPrefix (lookupDst input.family input.address)
    selection input peer) = _
  unfold decisionPrefix
  simp only [bind_assoc]
  apply congrArg
  funext accepted
  cases accepted <;> simp only [Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true,pure_bind,bind_assoc,suffix]
  apply congrArg
  funext peer
  exact selection_factor input peer

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front
