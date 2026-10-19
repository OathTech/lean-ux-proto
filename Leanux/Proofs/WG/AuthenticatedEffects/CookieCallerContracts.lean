import Leanux.Proofs.WG.AuthenticatedEffects.CookieSocketSource

/-! Caller obligations for the actual MAC gate. A cookie callback receives a
qualification proof only after the native load/MAC and packet-kind decisions;
an arbitrary invocation of that callback has no such contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CookieCaller
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def DecisionRun (action : WG.M Bool) (value : Bool) : Prop :=
  ∀ w a, ∃ b, (action.run w).run a = .ok ((value,w),b)

theorem branch_decides (site : Decision) (value : Bool) :
    DecisionRun (branch site value) value := by
  intro w a
  exact ⟨CounterWindow.record a site value,rfl⟩

theorem and_decides (left right : WG.M Bool) (a b : Bool)
    (ha : DecisionRun left a) (hb : DecisionRun right b) :
    DecisionRun (WG.andM left right) (a && b) := by
  intro w ambient
  obtain ⟨middle,hl⟩ := ha w ambient
  obtain ⟨last,hr⟩ := hb w middle
  cases a
  · exact ⟨middle,by simp [WG.andM,StateT.run_bind,hl]⟩
  · exact ⟨last,by simpa [WG.andM,StateT.run_bind,hl] using hr⟩

theorem or_decides (left right : WG.M Bool) (a b : Bool)
    (ha : DecisionRun left a) (hb : DecisionRun right b) :
    DecisionRun (WG.orM left right) (a || b) := by
  intro w ambient
  obtain ⟨middle,hl⟩ := ha w ambient
  obtain ⟨last,hr⟩ := hb w middle
  cases a
  · exact ⟨last,by simpa [WG.orM,StateT.run_bind,hl] using hr⟩
  · exact ⟨middle,by simp [WG.orM,StateT.run_bind,hl]⟩

theorem bind_decision (Safe : List E → Prop) (action : WG.M Bool) (value : Bool)
    (known : DecisionRun action value) (next : Bool → WGPrefix E α)
    (good : Driver.StateHistorySafe Safe (next value)) :
    Driver.StateHistorySafe Safe (liftWGPrefix action >>= next) := by
  have first : StatePrefixEnsures (fun h _ _ => Safe h) Safe (liftWGPrefix action)
      (fun result h _ _ => Safe h ∧ result = value) := by
    apply StatePrefixEnsures.lift (P := fun h _ _ => Safe h) (S := Safe) action (fun _ _ _ hi => hi)
    intro h w a result v b hi run
    obtain ⟨last,native⟩ := known w a
    rw [native] at run
    cases run
    exact ⟨hi,rfl⟩
  apply StatePrefixEnsures.bind first
  intro result
  intro w a h hi
  rcases hi with ⟨safe,rfl⟩
  exact good w a h safe

/-- Every non-cookie callback preserves the chosen history property. The
cookie callback is deliberately absent: its actual guarded callers prove it. -/
structure OtherSafe (Safe : List E → Prop) (o : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (action : WG.M α), o.step action = liftWGPrefix action
  session : ∀ pid, Driver.StateHistorySafe Safe (o.session pid)
  modifyPeer : ∀ pid f, Driver.StateHistorySafe Safe (o.modifyPeer pid f)
  create : ∀ pid, Driver.StateHistorySafe Safe (o.create pid)
  mac : ∀ pid msg, Driver.StateHistorySafe Safe (o.mac pid msg)
  send : ∀ pid msg, Driver.StateHistorySafe Safe (o.send pid msg)
  derived : ∀ pid, Driver.StateHistorySafe Safe (o.derived pid)
  traversal : ∀ pid, Driver.StateHistorySafe Safe (o.traversal pid)
  sent : ∀ pid, Driver.StateHistorySafe Safe (o.sent pid)
  initiation : ∀ msg, Driver.StateHistorySafe Safe (o.initiation msg)
  response : ∀ msg, Driver.StateHistorySafe Safe (o.response msg)
  endpoint : ∀ pid src, Driver.StateHistorySafe Safe (o.endpoint pid src)
  complete : ∀ pid, Driver.StateHistorySafe Safe (o.complete pid)
  keepalive : ∀ pid, Driver.StateHistorySafe Safe (o.keepalive pid)
  received : ∀ pid, Driver.StateHistorySafe Safe (o.received pid)
  put : ∀ pid, Driver.StateHistorySafe Safe (o.put pid)

theorem response (safe : OtherSafe Safe o) (pid : PeerId) :
    Driver.StateHistorySafe Safe (responseWith o pid) := by
  unfold responseWith
  simp only [safe.step]
  repeat' first
    | exact safe.session _
    | exact safe.modifyPeer _ _
    | exact safe.create _
    | exact safe.mac _ _
    | exact safe.send _ _
    | exact safe.derived _
    | exact safe.traversal _
    | exact safe.sent _
    | driver_state_history_step

open Lean Meta Elab Tactic in
elab "cookie_decision_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Driver.StateHistorySafe do throwError "not a history contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a source bind"
  let args := action.getAppArgs
  unless args.size ≥ 2 do throwError "missing bind action"
  let first := args[args.size - 2]!.consumeMData
  unless first.isAppOf ``liftWGPrefix do throwError "not a native lift"
  let native := first.getAppArgs.back!.consumeMData
  let .const actual _ := native.getAppFn | throwError "not a native constant"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different native source"

private theorem mac_beq_true (a b : MacState) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

theorem after_mac (safe : OtherSafe Safe o) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState)
    (cookie : loaded = true → state = .noCookie →
      (messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
        messageType msg = MESSAGE_HANDSHAKE_RESPONSE) →
      Driver.StateHistorySafe Safe (o.cookie msg src)) :
    Driver.StateHistorySafe Safe (afterMacWith o msg src loaded state) := by
  unfold afterMacWith
  simp only [safe.step]
  apply bind_decision _ _ _
    (or_decides _ _ _ _
      (and_decides _ _ _ _ (branch_decides _ _) (branch_decides _ _))
      (and_decides _ _ _ _ (branch_decides _ _) (branch_decides _ _)))
  repeat' first
    | (cookie_decision_head WG.andM; apply bind_decision _ _ _
        (and_decides _ _ _ _ (branch_decides _ _) (branch_decides _ _)))
    | (cookie_decision_head branch; apply bind_decision _ _ _ (branch_decides _ _))
    | (driver_history_head responseWith; exact response safe _)
    | (driver_history_head Ops.session; exact safe.session _)
    | (driver_history_head Ops.modifyPeer; exact safe.modifyPeer _ _)
    | (driver_history_head Ops.initiation; exact safe.initiation _)
    | (driver_history_head Ops.response; exact safe.response _)
    | (driver_history_head Ops.endpoint; exact safe.endpoint _ _)
    | (driver_history_head Ops.derived; exact safe.derived _)
    | (driver_history_head Ops.complete; exact safe.complete _)
    | (driver_history_head Ops.keepalive; exact safe.keepalive _)
    | (driver_history_head Ops.received; exact safe.received _)
    | (driver_history_head Ops.traversal; exact safe.traversal _)
    | (driver_history_head Ops.put; exact safe.put _)
    | (driver_history_head Ops.cookie; apply cookie <;>
        simp_all [Bool.and_eq_true,mac_beq_true])
    | simp +failIfUnchanged only [pure_bind]
    | driver_state_history_step

theorem receive (make : HandshakeMac → Ops (WGPrefix E))
    (other : ∀ mac, mac.checked.Valid (cookieValidatePacket mac.input mac.source mac.loaded) →
      OtherSafe Safe (make mac))
    (cookie : ∀ mac, mac.checked.Valid (cookieValidatePacket mac.input mac.source mac.loaded) →
      mac.loaded = true → mac.checked.value = .noCookie →
      (messageType mac.input = MESSAGE_HANDSHAKE_INITIATION ∨
        messageType mac.input = MESSAGE_HANDSHAKE_RESPONSE) →
      Driver.StateHistorySafe Safe ((make mac).cookie mac.input mac.source))
    (msg : Key) (src : SkbSource) :
    Driver.StateHistorySafe Safe (HandshakeWorker.receiveWith make msg src) := by
  unfold HandshakeWorker.receiveWith
  apply Driver.History.state_bind (Driver.History.state_lift _)
  intro isCookie
  split
  · exact Driver.History.state_bind (Driver.History.state_lift _)
      (fun _ => Driver.History.state_pure _)
  · apply Driver.History.state_bind (Driver.History.state_lift _)
    intro loaded
    have captured : StatePrefixEnsures (fun h _ _ => Safe h) Safe
        (captureWGRun (cookieValidatePacket msg src loaded))
        (fun receipt h _ _ => Safe h ∧ receipt.Valid (cookieValidatePacket msg src loaded)) := by
      apply StatePrefixEnsures.captureWGRun (P := fun h _ _ => Safe h) (S := Safe) _
        (fun _ _ _ hi => hi)
      intro h w a value v b hi run
      exact ⟨hi,run⟩
    apply StatePrefixEnsures.bind captured
    intro checked w a h hi
    exact after_mac (other ⟨msg,src,loaded,checked⟩ hi.2) msg src loaded checked.value
      (cookie ⟨msg,src,loaded,checked⟩ hi.2) w a h hi.1

theorem observed_history (Safe : List E → Prop) (record : CookieSocket.Receipt → E)
    (mac : HandshakeMac) (native : mac.checked.Valid (cookieValidatePacket mac.input mac.source mac.loaded))
    (loaded : mac.loaded = true) (state : mac.checked.value = .noCookie)
    (kind : messageType mac.input = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType mac.input = MESSAGE_HANDSHAKE_RESPONSE)
    (append : ∀ h receipt, Safe h → receipt.Valid → receipt.Qualifying →
      (messageType receipt.input = MESSAGE_HANDSHAKE_INITIATION ∨
        messageType receipt.input = MESSAGE_HANDSHAKE_RESPONSE) → Safe (h ++ [record receipt])) :
    Driver.StateHistorySafe Safe (CookieSocket.observed record mac mac.input mac.source) := by
  intro w a h hi
  obtain ⟨suffix,grown,bound,members⟩ := CookieSocket.observed_receipts record mac mac.input mac.source w a h
  have good : Safe (h ++ suffix) := by
    cases suffix with
    | nil => simpa only [List.append_nil] using hi
    | cons event rest =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at bound; omega)
      subst rest
      obtain ⟨receipt,rfl,valid,hm,hin,hsrc⟩ := members event (by simp)
      apply append h receipt hi valid
      · refine ⟨by rw [hm,hin],by rw [hm,hsrc],by rw [hm]; exact loaded,
          by rw [hm]; exact state,?_⟩
        simpa only [hm,hin,hsrc,loaded] using native
      · simpa only [hin] using kind
  change (runPrefix (StateT.run (CookieSocket.observed record mac mac.input mac.source) w) a h).2 = h ++ suffix at grown
  refine ⟨suffix,grown,grown ▸ good,?_⟩
  cases result : (runPrefix (StateT.run (CookieSocket.observed record mac mac.input mac.source) w) a h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨value,b⟩
    exact grown ▸ good

end Leanux.Proofs.WG.AuthenticatedEffects.CookieCaller
