import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionHandshakeH1
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverHandshakeFrames

/-! Existing C1 configured/slot frames are separated from the named C2
pending-slot effects. The finite labels used to forget C1's extra component
are a resident inventory, never an assumed confirmation history. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem Carrier.from_frame {action : WG.M α}
    (core : ∀ labels, Preserves (Responder.DriverCuts.Carrier labels) action)
    (pending : SameView view action) (confirmed : List Nat) : Preserves (Carrier confirmed) action :=
  Carrier.bounds confirmed (ResidentMaterial.bounds_forget core) (frame_preserves pending confirmed)

theorem Carrier.from_retained {action : WG.M α}
    (core : ∀ labels, Preserves (Responder.DriverCuts.Carrier labels) action)
    (pending : ProjectedAction view Retained action) (confirmed : List Nat) :
    Preserves (Carrier confirmed) action :=
  Carrier.bounds confirmed (ResidentMaterial.bounds_forget core) (PendingPromotion.preserves pending confirmed)

theorem cookie_frame {action : WG.M α} (same : Cookies.NoNoiseChange action) : SameView view action := by
  apply same.of_factor (fun s => view {dev := s.1,keypairCounter := s.2.2})
  intro w
  apply Store.ext
  · rfl
  · funext pid
    cases device : w.dev with
    | none => simp [view,nextSlot,Cookies.noiseView,Cookies.viewOfStore,wgStoreView,device]
    | some d =>
      simp only [Cookies.noiseView,Cookies.viewOfStore,wgStoreView,device,Option.map_some]
      have keys : keypairResidents {dev := some (Cookies.scrub d),keypairCounter := w.keypairCounter} =
          keypairResidents w := by
        funext kid
        simp only [keypairResidents,device,Option.bind_some]
        rfl
      change (nextSlot w pid).bind (keypairResidents w) =
        (nextSlot {dev := some (Cookies.scrub d),keypairCounter := w.keypairCounter} pid).bind
          (keypairResidents {dev := some (Cookies.scrub d),keypairCounter := w.keypairCounter})
      rw [keys]
      simp only [nextSlot,device,Option.bind_some]
      rfl

theorem Carrier.cookie {action : WG.M α} (same : Cookies.NoNoiseChange action) (confirmed : List Nat) :
    Preserves (Carrier confirmed) action :=
  Carrier.from_frame (Responder.DriverCuts.carrier_cookie same) (cookie_frame same) confirmed

theorem modify_device (f : Device → Device)
    (peers : ∀ d, (f d).peers = d.peers) (keys : ∀ d, (f d).keypairs = d.keypairs) :
    SameView view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases run
  have keySame : keypairResidents {w with dev := w.dev.map f} = keypairResidents w := by
    funext kid
    simp only [keypairResidents,Option.bind_map,Function.comp_def,keys]
  apply Store.ext
  · rfl
  · funext pid
    simp only [view,keySame,nextSlot,Option.bind_map,Function.comp_def,peers]

theorem Carrier.modify_device (f : Device → Device)
    (configured : ∀ d, ConfiguredIdentity.state (f d) = ConfiguredIdentity.state d)
    (front : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (peers : ∀ d, (f d).peers = d.peers) (keys : ∀ d, (f d).keypairs = d.keypairs)
    (confirmed : List Nat) : Preserves (Carrier confirmed) (modifyDev f) :=
  Carrier.from_frame (Responder.DriverCuts.carrier_modify f configured front peers keys)
    (PendingPromotion.modify_device f peers keys) confirmed

theorem ambient (action : AmbientM α) : Observed (liftWGPrefix (monadLift action)) :=
  native _ (fun confirmed => hoare_liftAmbient action (Carrier confirmed))

theorem pure (value : α) : Observed (pure value) :=
  StatePrefixEnsures.pure value (fun _ _ _ hi => hi.2.2.distinct) (fun _ _ _ hi => hi)

theorem same_world {action : WG.M α} (same : SameView id action) : Observed (liftWGPrefix action) :=
  native _ (fun confirmed => same.wp (Carrier confirmed))

theorem conditional (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : Observed a) (hb : Observed b) : Observed (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte] <;> assumption

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
