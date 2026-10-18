import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverCutFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderJointHistory

/-! Native hook receipts intended for a shared RX/TX execution journal. A
confirmation receipt is emitted before its consumer proceeds to staging. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged

inductive Event where
  | confirmed (pid : PeerId) (kid : KeypairId) (run : WGRunWitness Bool)
  | selected (pid : PeerId) (run : WGRunWitness (Option (Peer × Option KeypairId)))
  | session (pid : PeerId) (run : WGRunWitness Bool)

def Event.Valid : Event → Prop
  | .confirmed pid kid r => r.Valid (receivedWithKeypair pid kid)
  | .selected pid r => r.Valid (selectionPrefix pid)
  | .session pid r => r.Valid (beginSession pid)

def Event.labels : Event → List Nat
  | .confirmed _ kid r => confirmedAt r.before kid r.value
  | _ => []

def labels (h : List Event) : List Nat := h.flatMap Event.labels

def confirmation (pid : PeerId) (kid : KeypairId) : WGPrefix Event Bool :=
  receiptWGObserved (liftWGPrefix (receivedWithKeypair pid kid)) (.confirmed pid kid)

def selection (pid : PeerId) : WGPrefix Event (Option (Peer × Option KeypairId)) :=
  receiptWGObserved (liftWGPrefix (selectionPrefix pid)) (.selected pid)

def session (pid : PeerId) : WGPrefix Event Bool :=
  receiptWGObserved (liftWGPrefix (beginSession pid)) (.session pid)

theorem confirmation_erases (pid : PeerId) (kid : KeypairId) :
    ErasesStatePrefix (confirmation pid kid) (receivedWithKeypair pid kid) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem selection_erases (pid : PeerId) :
    ErasesStatePrefix (selection pid) (selectionPrefix pid) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem session_erases (pid : PeerId) :
    ErasesStatePrefix (session pid) (beginSession pid) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

/-- Every normal callback records its actual source execution once. A source
Stop emits nothing, leaving any prior prefix intact. -/
theorem receipt_run (action : WG.M α) (make : WGRunWitness α → Event)
    (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (receiptWGObserved (liftWGPrefix action) make) w a h =
      match (action.run w).run a with
      | .error stop => (.error stop, h)
      | .ok ((value, v), b) =>
        (.ok ((value, v), b), h ++ [make ⟨value, w, v, a, b⟩]) := by
  rw [runWGPrefix_receiptWGObserved, runWGPrefix_lift]
  cases (action.run w).run a with
  | error stop => rfl
  | ok out => rcases out with ⟨⟨value, v⟩, b⟩; rfl

/-- The inner native confirmation updates authorization before any caller
continuation, using labels from this exact journal, including confirmation in a
consumer that later stops. Initialized transport and AEAD provenance are not
premises hidden in this local contract. -/
theorem confirmation_authorizes (H1 : H1ResponderCurrentEdges)
    (pid : PeerId) (kid : KeypairId) (w : WGWorld) (a : Ambient) (h : List Event)
    (entry : History.Native (labels h) w) :
    match (runWGPrefix (confirmation pid kid) w a h).1 with
    | .error _ => True
    | .ok ((_, v), _) =>
      History.Native (labels (runWGPrefix (confirmation pid kid) w a h).2) v := by
  unfold confirmation
  rw [receipt_run]
  cases run : ((receivedWithKeypair pid kid).run w).run a with
  | error stop => trivial
  | ok out =>
    rcases out with ⟨⟨value, v⟩, b⟩
    simpa [labels, Event.labels, List.flatMap_append] using
      confirmation_native H1 pid kid (labels h) ⟨value, w, v, a, b⟩ run entry

/-- Native session creation preserves authorization with the configured-peer
and slot hypotheses exposed at the source cut. The initialized caller must
derive these facts rather than assume them for a whole trace. -/
theorem session_authorizes (H1 : H1ResponderCurrentEdges) (pid : PeerId)
    (confirmed : List Nat) (r : WGRunWitness Bool)
    (entry : ConfiguredIdentity.Inv r.before ∧ History.Native confirmed r.before)
    (valid : r.Valid (beginSession pid)) : History.Native confirmed r.after :=
  (Leanux.Proofs.Framing.hoare_iff_run_ambient _ _ _).mp
    (Joint.session_native H1 pid confirmed) _ _ _ _ _ entry valid

/-- A later stopped continuation cannot erase a previously completed native
confirmation receipt. This is an ordering fact about the same journal. -/
theorem confirmation_retained (pid : PeerId) (kid : KeypairId)
    (w v : WGWorld) (a b : Ambient) (h : List Event) (value : Bool)
    (run : ((receivedWithKeypair pid kid).run w).run a = .ok ((value, v), b))
    (next : Bool → WGPrefix Event α) (appends : ∀ value, StateAppends (next value)) :
    ∃ suffix, (runWGPrefix (confirmation pid kid >>= next) w a h).2 =
      h ++ [.confirmed pid kid ⟨value, w, v, a, b⟩] ++ suffix := by
  obtain ⟨suffix, hs⟩ := appends value v b (h ++ [.confirmed pid kid ⟨value, w, v, a, b⟩])
  refine ⟨suffix, ?_⟩
  change (runStatePrefix (confirmation pid kid >>= next) w a h).2 = _
  rw [runStatePrefix_bind]
  have equation := receipt_run (receivedWithKeypair pid kid) (Event.confirmed pid kid) w a h
  change runStatePrefix (confirmation pid kid) w a h = _ at equation
  rw [equation, run]
  exact hs

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
