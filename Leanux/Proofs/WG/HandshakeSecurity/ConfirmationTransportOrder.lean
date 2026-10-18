import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverCuts
import Leanux.Proofs.WG.AuthenticatedEffects.TransportConfirmationEntry

/-! Confirmation attribution in one shared journal. The native confirmation
receipt is tied to the immediately preceding successful replay check. A
separate safety property of the same journal supplies its AEAD publication. This module is generic over event
constructors and does not import the combined driver journal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects
abbrev ResponderEvent := Responder.DriverCuts.Event
variable {E : Type}

def Accepted (recordReplay : TransportDriver.Replay → E) (pid : PeerId) (kid : KeypairId)
    (h : List E) : Prop :=
  ∃ pre r, h = pre ++ [recordReplay r] ∧ r.packet.peer = pid ∧ r.packet.keypair = kid ∧
    r.run.value = true

def Checked (recordReplay : TransportDriver.Replay → E) (decode : E → Option ResponderEvent)
    (pre : List E) (event : E) : Prop :=
  ∀ pid kid r, decode event = some (.confirmed pid kid r) →
    r.Valid (receivedWithKeypair pid kid) ∧ Accepted recordReplay pid kid pre

def Safe (recordReplay : TransportDriver.Replay → E) (decode : E → Option ResponderEvent)
    (history : List E) : Prop :=
  ∀ pre event post, history = pre ++ event :: post → Checked recordReplay decode pre event

theorem Safe.append {recordReplay : TransportDriver.Replay → E} {decode : E → Option ResponderEvent}
    {h suffix : List E} (hi : Safe recordReplay decode h)
    (next : ∀ pre event post, suffix = pre ++ event :: post →
      Checked recordReplay decode (h ++ pre) event) : Safe recordReplay decode (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    (Checked recordReplay decode) h suffix hi next

def Unconfirmed (decode : E → Option ResponderEvent) (event : E) : Prop :=
  ∀ pid kid r, decode event ≠ some (.confirmed pid kid r)

theorem Safe.quiet {recordReplay : TransportDriver.Replay → E} {decode : E → Option ResponderEvent}
    {h suffix : List E} (hi : Safe recordReplay decode h)
    (quiet : ∀ event ∈ suffix, Unconfirmed decode event) :
    Safe recordReplay decode (h ++ suffix) := by
  apply hi.append
  intro pre event post position pid kid r found
  have member : event ∈ suffix := by rw [position]; simp
  exact False.elim (quiet event member pid kid r found)

theorem Safe.confirmation {recordReplay : TransportDriver.Replay → E} {decode : E → Option ResponderEvent}
    {history pre post : List E} {event : E} {pid : PeerId} {kid : KeypairId} {r : WGRunWitness Bool}
    (safe : Safe recordReplay decode history)
    (position : history = pre ++ event :: post)
    (recorded : decode event = some (.confirmed pid kid r)) :
    r.Valid (receivedWithKeypair pid kid) ∧ Accepted recordReplay pid kid pre :=
  safe pre event post position pid kid r recorded

theorem state_lift (recordReplay : TransportDriver.Replay → E) (decode : E → Option ResponderEvent)
    (action : WG.M α) :
    StatePrefixPreserves (fun h _ _ => Safe recordReplay decode h)
      (Safe recordReplay decode) (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi)

theorem product_lift (recordReplay : TransportDriver.Replay → E) (decode : E → Option ResponderEvent)
    (action : Leanux.M α) :
    PrefixPreserves (fun h _ => Safe recordReplay decode h)
      (Safe recordReplay decode) (liftPrefix action) :=
  (PrefixEnsures.lift (P := fun h (_ : World) => Safe recordReplay decode h)
    (Q := fun _ h (_ : World) => Safe recordReplay decode h) action
    (fun _ _ hi => hi) (fun _ _ _ _ hi _ => hi)).preserves


def confirmation (record : ResponderEvent → E) (decode : E → Option ResponderEvent)
    (pid : PeerId) (kid : KeypairId) : WGPrefix E Bool :=
  focusStatePrefix record decode (Responder.DriverCuts.confirmation pid kid)

theorem confirmation_run (record : ResponderEvent → E) (decode : E → Option ResponderEvent)
    (pid : PeerId) (kid : KeypairId) (w : WGWorld) (a : Ambient) (h : List E) :
    runWGPrefix (confirmation record decode pid kid) w a h =
      match ((receivedWithKeypair pid kid).run w).run a with
      | .error stop => (.error stop,h)
      | .ok ((value,v),b) =>
        (.ok ((value,v),b),h ++ [record (.confirmed pid kid ⟨value,w,v,a,b⟩)]) := by
  have equation := Responder.DriverCuts.receipt_run (receivedWithKeypair pid kid)
    (Responder.DriverCuts.Event.confirmed pid kid) w a (h.filterMap decode)
  change runWGPrefix (Responder.DriverCuts.confirmation pid kid) w a (h.filterMap decode) = _ at equation
  change ((runWGPrefix (Responder.DriverCuts.confirmation pid kid) w a _).1,
    h ++ ((runWGPrefix (Responder.DriverCuts.confirmation pid kid) w a _).2.drop _).map record) = _
  rw [equation]
  cases run : ((receivedWithKeypair pid kid).run w).run a with
  | error stop => simp
  | ok out => rcases out with ⟨⟨value,v⟩,b⟩; simp

theorem confirmation_checked (recordReplay : TransportDriver.Replay → E) (record : ResponderEvent → E)
    (decode : E → Option ResponderEvent) (inverse : ∀ event, decode (record event) = some event)
    (pid : PeerId) (kid : KeypairId) :
    StatePrefixEnsures
      (fun h _ _ => Safe recordReplay decode h ∧ Accepted recordReplay pid kid h)
      (Safe recordReplay decode) (confirmation record decode pid kid)
      (fun _ h _ _ => Safe recordReplay decode h) := by
  intro w a h hi
  have equation := confirmation_run record decode pid kid w a h
  unfold runWGPrefix runStatePrefix at equation
  rw [equation]
  cases run : ((receivedWithKeypair pid kid).run w).run a with
  | error stop => exact ⟨[],by simp,hi.1,trivial⟩
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    let r : WGRunWitness Bool := ⟨value,w,v,a,b⟩
    have safe : Safe recordReplay decode (h ++ [record (.confirmed pid kid r)]) := by
      apply hi.1.append
      intro pre event post position peer key receipt found
      cases pre with
      | nil =>
        cases position
        rw [inverse] at found
        cases found
        exact ⟨run,by simpa only [List.append_nil] using hi.2⟩
      | cons x xs =>
        have lengths := congrArg List.length position
        simp only [List.length_append,List.length_cons,List.length_nil] at lengths
        omega
    exact ⟨[record (.confirmed pid kid r)],rfl,safe,safe⟩

theorem confirmation_from_input (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (recordReplay : TransportDriver.Replay → E)
    (record : ResponderEvent → E) (decode : E → Option ResponderEvent)
    (inverse : ∀ event, decode (record event) = some event) (pid : PeerId) (kid : KeypairId) :
    PrefixEnsures
      (fun h w => Safe recordReplay decode h ∧
        TransportReplay.ConfirmationInput origin replay recordReplay pid kid h w)
      (Safe recordReplay decode) (liftWGObserver (confirmation record decode pid kid))
      (fun _ h _ => Safe recordReplay decode h) :=
  (confirmation_checked recordReplay record decode inverse pid kid).liftWGObserver.consequence
    (fun _ _ hi => by
      obtain ⟨pre,r,position,peer,key,result,_⟩ := TransportReplay.confirmation_input_authenticated hi.2
      exact ⟨hi.1,pre,r,position,peer,key,result⟩)
    (fun _ _ _ hi => hi)

/-- Two independently established properties of the same concrete journal
join at the exact counter occurrence immediately preceding confirmation. -/
theorem authenticated (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (recordReplay : TransportDriver.Replay → E)
    (decode : E → Option ResponderEvent) (inverse : ∀ r, replay (recordReplay r) = some r)
    (history pre post : List E) (event : E) (pid : PeerId) (kid : KeypairId) (r : WGRunWitness Bool)
    (ordered : Safe recordReplay decode history) (accepted : TransportReplay.Safe origin replay history)
    (position : history = pre ++ event :: post)
    (recorded : decode event = some (.confirmed pid kid r)) :
    r.Valid (receivedWithKeypair pid kid) ∧
    ∃ earlier counter, pre = earlier ++ [recordReplay counter] ∧
      counter.packet.peer = pid ∧ counter.packet.keypair = kid ∧ counter.run.value = true ∧
      TransportReplay.Certified (earlier.filterMap origin) counter := by
  obtain ⟨valid,earlier,counter,immediate,peer,key,result⟩ := ordered.confirmation position recorded
  refine ⟨valid,earlier,counter,immediate,peer,key,result,?_⟩
  apply TransportReplay.replay_authenticated accepted (pre := earlier)
    (event := recordReplay counter) (post := event :: post) _ (inverse counter)
  simp only [position,immediate,List.append_assoc,List.singleton_append]

end Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder
