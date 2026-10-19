import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalSource
import Leanux.Proofs.WG.Origins.HandshakeSources
import Leanux.Proofs.WG.Lifetimes.MaintenanceTimers

/-! Instantiate the original handshake source factories with session and hook receipts. All other operations are original lifts. Erasure includes Stops and the receive-step false return. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Origins

def ops : HandshakeSources.Ops Obs where
  step := liftWGPrefix
  session := session
  modifyPeer := fun pid f => liftWGPrefix (do setPeer pid (f (← getPeer pid)))
  create := fun pid => liftWGPrefix (createResponse pid)
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  derived := hook .sessionDerived
  traversal := hook .traversal
  sent := hook .authenticatedSent
  cookie := fun msg src => liftWGPrefix (sendHandshakeCookie msg src)
  initiation := fun msg => liftWGPrefix (consumeInitiation msg)
  response := fun msg => liftWGPrefix (consumeResponse msg)
  endpoint := fun pid src => liftWGPrefix (setPeerEndpointFromSkb pid src)
  complete := hook (.handshakeComplete .walltimeLastHandshake)
  keepalive := fun pid => liftWGPrefix (sendKeepalive pid)
  received := hook .authenticatedReceived
  put := fun peer => liftWGPrefix (peerPut peer)
  cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)
def response (pid : PeerId) : Obs Unit := HandshakeSources.responseWith ops pid
def afterMac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) : Obs Unit :=
  HandshakeSources.afterMacWith ops msg src loaded mac
def reception (msg : List UInt8) (src : SkbSource) : Obs Unit :=
  HandshakeSources.receptionWith ops msg src
def step : Obs Bool := HandshakeSources.stepWith ops
theorem response_eq (pid : PeerId) : response pid=HandshakeSources.responseWith ops pid := rfl
theorem afterMac_eq (msg src loaded mac) : afterMac msg src loaded mac=HandshakeSources.afterMacWith ops msg src loaded mac := rfl
theorem reception_eq (msg src) : reception msg src=HandshakeSources.receptionWith ops msg src := rfl
macro "journal_erase_atom" : tactic => `(tactic|
  first
    | (maintenance_head session; exact session_erases _)
    | (maintenance_head hook; exact hook_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
    | maintenance_intro
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | contradiction
    | rfl)
theorem response_erases (pid : PeerId) :
    ErasesStatePrefix (response pid) (sendHandshakeResponse pid) := by
  rw [←HandshakeSources.response_original]
  unfold response HandshakeSources.responseWith
  dsimp (config:={zeta:=false}) only [ops,HandshakeSources.original]
  repeat' journal_erase_atom
theorem afterMac_erases (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    ErasesStatePrefix (afterMac msg src loaded mac) (Cookies.afterMac msg src loaded mac) := by
  rw [←HandshakeSources.afterMac_original]
  unfold afterMac HandshakeSources.afterMacWith
  simp (config:={zeta:=false}) only [←response_eq,HandshakeSources.response_original]
  change ErasesStatePrefix _ _
  dsimp (config:={zeta:=false}) only [ops,HandshakeSources.original]
  repeat' first | (maintenance_head response; exact response_erases _) | journal_erase_atom
theorem reception_erases (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (reception msg src) (receiveHandshakePacket msg src) := by
  rw [←HandshakeSources.reception_original]
  unfold reception HandshakeSources.receptionWith
  simp (config:={zeta:=false}) only [←afterMac_eq,HandshakeSources.afterMac_original]
  dsimp (config:={zeta:=false}) only [ops,HandshakeSources.original]
  repeat' first | (maintenance_head afterMac; exact afterMac_erases _ _ _ _) | journal_erase_atom
theorem step_erases : ErasesStatePrefix step receiveStep := by
  rw [←HandshakeSources.step_original]
  unfold step HandshakeSources.stepWith
  simp only [←reception_eq,HandshakeSources.reception_original]
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro d
  cases d.handshakeQueue.consume with
  | mk packet ring =>
    cases packet with
    | none =>
      exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _=>erasesStatePrefix_pure _)
    | some packet =>
      obtain ⟨msg,src⟩:=packet
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro _
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro _
      apply erasesStatePrefix_bind (reception_erases msg src)
      intro _
      exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _=>erasesStatePrefix_pure _)
theorem lift_valid {α : Type} (a : WG.M α) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ prior=>prior) (fun _ _ _ _ _ _ prior _=>prior)
theorem pure_valid {α : Type} (x : α) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (pure x : Obs α) :=
  StatePrefixEnsures.pure x (fun _ _ _ prior=>prior) (fun _ _ _ prior=>prior)
macro "journal_valid" : tactic => `(tactic|
  repeat' first
    | (maintenance_head session; exact session_valid _)
    | (maintenance_head hook; exact hook_valid _ _)
    | (maintenance_head liftWGPrefix; exact lift_valid _)
    | (maintenance_head Pure.pure; exact pure_valid _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q:=fun _ h _ _=>ValidHistory h))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction)
theorem response_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (response pid) := by
  unfold response HandshakeSources.responseWith
  dsimp (config:={zeta:=false}) only [ops]
  change StatePrefixEnsures _ _ _ (fun _ h _ _=>ValidHistory h)
  journal_valid
theorem afterMac_valid (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (afterMac msg src loaded mac) := by
  unfold afterMac HandshakeSources.afterMacWith HandshakeSources.responseWith
  dsimp (config:={zeta:=false}) only [ops]
  change StatePrefixEnsures _ _ _ (fun _ h _ _=>ValidHistory h)
  journal_valid
theorem reception_valid (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (reception msg src) := by
  unfold reception HandshakeSources.receptionWith
  apply StatePrefixEnsures.bind (lift_valid _)
  intro cookie
  split
  · exact StatePrefixEnsures.bind (lift_valid _) (fun _=>pure_valid _)
  · apply StatePrefixEnsures.bind (lift_valid _)
    intro loaded
    apply StatePrefixEnsures.bind (lift_valid _)
    intro mac
    exact afterMac_valid msg src loaded mac
theorem step_valid :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory step := by
  unfold step HandshakeSources.stepWith
  apply StatePrefixEnsures.bind (lift_valid _)
  intro d
  cases d.handshakeQueue.consume with
  | mk packet ring =>
    cases packet with
    | none => exact StatePrefixEnsures.bind (lift_valid _) (fun _=>pure_valid _)
    | some packet =>
      obtain ⟨msg,src⟩:=packet
      apply StatePrefixEnsures.bind (lift_valid _)
      intro _
      apply StatePrefixEnsures.bind (lift_valid _)
      intro _
      apply StatePrefixEnsures.bind (reception_valid msg src)
      intro _
      exact StatePrefixEnsures.bind (lift_valid _) (fun _=>pure_valid _)

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
