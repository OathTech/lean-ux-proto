import Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumptionSource
import Leanux.Proofs.WG.AuthenticatedEffects.CookieCallerContracts

/-! The native cookie branch has its own callback contract. Qualification of
cookie replies still follows the actual load, MAC and packet-kind guards. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumption
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Origins.HandshakeSources CookieCaller

theorem receive_history
    (consume : Key → WGPrefix E Unit)
    (consumeSafe : ∀ msg, Driver.StateHistorySafe Safe (consume msg))
    (make : HandshakeMac → Ops (WGPrefix E))
    (other : ∀ mac, mac.checked.Valid (cookieValidatePacket mac.input mac.source mac.loaded) →
      OtherSafe Safe (make mac))
    (cookie : ∀ mac, mac.checked.Valid (cookieValidatePacket mac.input mac.source mac.loaded) →
      mac.loaded = true → mac.checked.value = .noCookie →
      (messageType mac.input = MESSAGE_HANDSHAKE_INITIATION ∨
        messageType mac.input = MESSAGE_HANDSHAKE_RESPONSE) →
      Driver.StateHistorySafe Safe ((make mac).cookie mac.input mac.source))
    (msg : Key) (src : SkbSource) :
    Driver.StateHistorySafe Safe (receiveWith consume make msg src) := by
  unfold receiveWith
  apply Driver.History.state_bind (Driver.History.state_lift _)
  intro isCookie
  split
  · exact Driver.History.state_bind (consumeSafe msg)
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


theorem observed_history (Safe : List E → Prop) (record : Receipt → E) (msg : Key)
    (append : ∀ h receipt, Safe h → receipt.Valid → Safe (h ++ [record receipt])) :
    Driver.StateHistorySafe Safe (observed record msg) := by
  intro w a h hi
  unfold observed
  have hr := runWGPrefix_receiptWGObserved (liftWGPrefix (cookieMessageConsume msg))
    (fun run => record ⟨msg,run⟩) w a h
  rw [runWGPrefix_lift] at hr
  simp only [runWGPrefix,runStatePrefix] at hr
  rw [hr]
  cases run : ((cookieMessageConsume msg).run w).run a with
  | error stop => exact ⟨[],by simp,hi,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have good := append h ⟨msg,⟨value,w,v,a,b⟩⟩ hi run
    exact ⟨[record ⟨msg,⟨value,w,v,a,b⟩⟩],rfl,good,good⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumption
