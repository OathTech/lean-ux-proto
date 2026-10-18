import Leanux.Proofs.WG.AuthenticatedEffects.TunnelObservation

/-! The reply sockets observe the final native append, not the call attempt.
Every native guard remains in the prefix before the tunnel observer. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Lifetimes

theorem liftWG_bind_run (action : WG.M α) (next : α → WGPrefix E β)
    (w : WGWorld) (a : Ambient) (h : List E) :
    runWGPrefix (liftWGPrefix action >>= next) w a h =
      match (action.run w).run a with
      | .error err => (.error err,h)
      | .ok ((x,u),b) => runWGPrefix (next x) u b h := by
  simp only [runWGPrefix,runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift]
  cases (action.run w).run a <;> rfl

theorem bind_pure_history (action : WGPrefix E α) (f : α → β)
    (w : WGWorld) (a : Ambient) (h : List E) :
    (runWGPrefix (action >>= fun x => pure (f x)) w a h).2 =
      (runWGPrefix action w a h).2 := by
  change (runStatePrefix _ w a h).2 = _
  rw [runStatePrefix_bind]
  change _ = (runStatePrefix action w a h).2
  cases runStatePrefix action w a h with
  | mk result hist => cases result <;> rfl

def socketEmitted (front : WG.M (Except Int Route)) (e : Endpoint)
    (bytes : List UInt8) (ds : Nat) : WGPrefix DatagramReceipt Int := do
  match ← liftWGPrefix front with
  | .error err => pure err
  | .ok route => tunnelObserved e bytes ds route; pure 0

theorem socketEmitted_erases (front : WG.M (Except Int Route)) (e : Endpoint)
    (bytes : List UInt8) (ds : Nat) :
    ErasesStatePrefix (socketEmitted front e bytes ds)
      (front >>= socketResult e bytes ds false) := by
  apply erasesStatePrefix_bind (erasesStatePrefix_lift front)
  intro result
  cases result with
  | error err => exact erasesStatePrefix_pure err
  | ok route =>
    exact erasesStatePrefix_bind (tunnelObserved_erases e bytes ds route)
      (fun _ => erasesStatePrefix_pure 0)

theorem socketEmitted_receipts (front : WG.M (Except Int Route)) (e : Endpoint)
    (bytes : List UInt8) (ds : Nat) (w : WGWorld) (a : Ambient) (h : List DatagramReceipt) :
    ∃ suffix, (runWGPrefix (socketEmitted front e bytes ds) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix,
        r.Valid ∧ r.endpoint = e ∧ r.bytes = bytes ∧ r.ds = ds := by
  unfold socketEmitted
  change ∃ suffix, (runStatePrefix _ w a h).2 = _ ∧ _ ∧ _
  rw [runStatePrefix_bind]
  have lift := runWGPrefix_lift (E := DatagramReceipt) front w a h
  change runStatePrefix _ w a h = _ at lift
  rw [lift]
  cases native : (front.run w).run a with
  | error err => exact ⟨[],by simp⟩
  | ok out =>
    rcases out with ⟨⟨result,u⟩,b⟩
    cases result with
    | error err => exact ⟨[],by simp⟩
    | ok route =>
      change ∃ suffix,
        (runWGPrefix (tunnelObserved e bytes ds route >>= fun _ => pure (0 : Int)) u b h).2 =
          h ++ suffix ∧ _ ∧ _
      rw [bind_pure_history]
      obtain ⟨suffix,eq,len,members⟩ := tunnelObserved_receipts e bytes ds route u b h
      exact ⟨suffix,eq,len,fun r mem =>
        ⟨(members r mem).1,(members r mem).2.1,(members r mem).2.2.1,(members r mem).2.2.2.1⟩⟩

def send4Emitted (e : Endpoint) (bytes : List UInt8) (ds : Nat) : WGPrefix DatagramReceipt Int :=
  socketEmitted (socket4Front e none bytes ds false) e bytes ds

def send6Emitted (e : Endpoint) (bytes : List UInt8) (ds : Nat) : WGPrefix DatagramReceipt Int :=
  socketEmitted (socket6Front e none) e bytes ds

theorem send4Emitted_erases (e : Endpoint) (bytes : List UInt8) (ds : Nat) :
    ErasesStatePrefix (send4Emitted e bytes ds) (send4 e none bytes ds false) := by
  rw [←send4Source_eq,socket4Front_factor]
  exact socketEmitted_erases _ _ _ _

theorem send6Emitted_erases (e : Endpoint) (bytes : List UInt8) (ds : Nat) :
    ErasesStatePrefix (send6Emitted e bytes ds) (send6 e none bytes ds false) := by
  rw [socket6_factor]
  exact socketEmitted_erases _ _ _ _

end Leanux.Proofs.WG.AuthenticatedEffects
