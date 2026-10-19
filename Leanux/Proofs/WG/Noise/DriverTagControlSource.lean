import Leanux.Proofs.WG.Noise.DriverTagControlFactors
import Leanux.Proofs.WG.Noise.DriverTagControlFrames
import Leanux.Proofs.WG.Noise.DriverTagLeafFrames

set_option autoImplicit false
/-! Source factors and exact all-outcome erasure. -/
namespace Leanux.Proofs.WG.Noise.DriverTags.Control
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
universe u

theorem stopPrefix_factor : wgStopPrefix =
    stopWith (fun {_} a => liftWGPrefix a)
      (stopPeerWith (fun pid => requireNotPendingMixed pid "wg_stop while a handshake is queued")
        purgeStagedPacketsPrefix timersStopPrefix handshakeClearPrefix
        keypairsClearPrefix resetLastSentHandshakePrefix) := by
  simp only [wgStopPrefix, stopWith, stopPeerWith, bind_assoc]

theorem downPrefix_factor : wgDownPrefix =
    downWith (fun {_} a => liftWGPrefix a) wgStopPrefix := rfl

theorem stopPeerWith_erases {E : Type}
    (required purge timers clear keys reset : PeerId → WGPrefix E Unit)
    (required' purge' timers' clear' keys' reset' : PeerId → WG.M Unit)
    (hr : ∀ pid, ErasesStatePrefix (required pid) (required' pid))
    (hp : ∀ pid, ErasesStatePrefix (purge pid) (purge' pid))
    (ht : ∀ pid, ErasesStatePrefix (timers pid) (timers' pid))
    (hc : ∀ pid, ErasesStatePrefix (clear pid) (clear' pid))
    (hk : ∀ pid, ErasesStatePrefix (keys pid) (keys' pid))
    (hz : ∀ pid, ErasesStatePrefix (reset pid) (reset' pid)) (pid : PeerId) :
    ErasesStatePrefix (stopPeerWith required purge timers clear keys reset pid)
      (stopPeerWith required' purge' timers' clear' keys' reset' pid) := by
  unfold stopPeerWith
  exact erasesStatePrefix_bind (hr pid) (fun _ =>
    erasesStatePrefix_bind (hp pid) (fun _ =>
    erasesStatePrefix_bind (ht pid) (fun _ =>
    erasesStatePrefix_bind (hc pid) (fun _ =>
    erasesStatePrefix_bind (hk pid) (fun _ => hz pid)))))

theorem stopWith_erases {E : Type} (peer : PeerId → WGPrefix E Unit)
    (peer' : PeerId → WG.M Unit)
    (hp : ∀ pid, ErasesStatePrefix (peer pid) (peer' pid)) :
    ErasesStatePrefix (stopWith (fun {_} a => liftWGPrefix a) peer)
      (stopWith (fun {_} a => a) peer') := by
  unfold stopWith
  repeat' first
    | with_reducible exact hp _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem downWith_erases {E : Type} (stop : WGPrefix E Unit) (stop' : WG.M Unit)
    (hs : ErasesStatePrefix stop stop') :
    ErasesStatePrefix (downWith (fun {_} a => liftWGPrefix a) stop)
      (downWith (fun {_} a => a) stop') :=
  erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => hs)

end Leanux.Proofs.WG.Noise.DriverTags.Control


/-! Generic source-preservation joins. -/
namespace Leanux.Proofs.WG.Noise.DriverTags.Control
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

theorem stopPeerWith_preserves {E : Type}
    (I : List E → WGWorld → Ambient → Prop) (S : List E → Prop)
    (required purge timers clear keys reset : PeerId → WGPrefix E Unit)
    (hr : ∀ pid, StatePrefixPreserves I S (required pid))
    (hp : ∀ pid, StatePrefixPreserves I S (purge pid))
    (ht : ∀ pid, StatePrefixPreserves I S (timers pid))
    (hc : ∀ pid, StatePrefixPreserves I S (clear pid))
    (hk : ∀ pid, StatePrefixPreserves I S (keys pid))
    (hz : ∀ pid, StatePrefixPreserves I S (reset pid)) (pid : PeerId) :
    StatePrefixPreserves I S (stopPeerWith required purge timers clear keys reset pid) := by
  unfold stopPeerWith
  exact (hr pid).bind (fun _ => (hp pid).bind (fun _ => (ht pid).bind
    (fun _ => (hc pid).bind (fun _ => (hk pid).bind (fun _ => hz pid)))))

/-- Only the concrete administrative stop leaves are assumptions. The body
callback is invoked once per saved-list element, in the original order. -/
theorem stopWith_preserves {E : Type}
    (I : List E → WGWorld → Ambient → Prop) (S : List E → Prop)
    (safe : ∀ h g ambient, I h g ambient → S h)
    (peer : PeerId → WGPrefix E Unit)
    (hp : ∀ pid, StatePrefixPreserves I S (peer pid))
    (read : StatePrefixPreserves I S (liftWGPrefix getDev))
    (iter : ∀ b, StatePrefixPreserves I S (liftWGPrefix (branch .stopPeersIter b)))
    (blocked : StatePrefixPreserves I S (liftWGPrefix
      (unsupported "wg_stop with handshake messages queued for the receive worker (its timing)" : WG.M Unit)))
    (drain : StatePrefixPreserves I S (liftWGPrefix (branch .stopDrainIter false)))
    (reset : StatePrefixPreserves I S (liftWGPrefix (modifyDev fun d => {d with handshakeQueueLen := 0})))
    (socket : StatePrefixPreserves I S (liftWGPrefix (socketReinit none none))) :
    StatePrefixPreserves I S (stopWith (fun {_} a => liftWGPrefix a) peer) := by
  have pure' {α : Type} (x : α) : StatePrefixPreserves I S (pure x : WGPrefix E α) :=
    StatePrefixEnsures.pure x safe (fun _ _ _ prior => prior)
  have loop (pids : List PeerId) :
      StatePrefixPreserves I S
        (forIn pids PUnit.unit (fun pid _ => do
          _ ← liftWGPrefix (branch .stopPeersIter true)
          peer pid
          pure (ForInStep.yield PUnit.unit)) : WGPrefix E PUnit) := by
    apply StatePrefixEnsures.forInInvariant (I := fun _ => I)
    · exact fun _ => safe
    · intro pid acc
      exact (iter true).bind (fun _ => (hp pid).bind (fun _ => pure' _))
  unfold stopWith
  apply read.bind
  intro d
  apply (loop d.peerList).bind
  intro _
  apply (iter false).bind
  intro _
  apply read.bind
  intro d
  dsimp only
  split
  · exact blocked.bind (fun _ => drain.bind (fun _ => reset.bind (fun _ => socket)))
  · exact drain.bind (fun _ => reset.bind (fun _ => socket))

theorem downWith_preserves {E : Type}
    (I : List E → WGWorld → Ambient → Prop) (S : List E → Prop)
    (stop : WGPrefix E Unit) (hs : StatePrefixPreserves I S stop)
    (running : StatePrefixPreserves I S
      (liftWGPrefix (modifyDev fun d => {d with running := false}))) :
    StatePrefixPreserves I S (downWith (fun {_} a => liftWGPrefix a) stop) :=
  running.bind (fun _ => hs)

end Leanux.Proofs.WG.Noise.DriverTags.Control


/-! Concrete stop leaves and the explicit timer observer callback. -/
namespace Leanux.Proofs.WG.Noise.DriverTags.Control
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def stopPeerObservedWith (timers : PeerId → Obs Unit) (pid : PeerId) : Obs Unit :=
  stopPeerWith
    (fun pid => liftWGPrefix (requireNotPending pid "wg_stop while a handshake is queued"))
    (fun pid => liftWGPrefix (purgeStagedPackets pid)) timers
    (fun pid => recordHelper (.handshakeClear pid) (fun _ => .cleared) (handshakeClear pid))
    (fun pid => liftWGPrefix (keypairsClear pid))
    (fun pid => liftWGPrefix (resetLastSentHandshake pid)) pid

def stopObservedWith (timers : PeerId → Obs Unit) : Obs Unit :=
  stopWith (fun {_} a => liftWGPrefix a) (stopPeerObservedWith timers)

def downObservedWith (timers : PeerId → Obs Unit) : Obs Unit :=
  downWith (fun {_} a => liftWGPrefix a) (stopObservedWith timers)

theorem stopPeerObservedWith_erases (timers : PeerId → Obs Unit)
    (ht : ∀ pid, ErasesStatePrefix (timers pid) (timersStop pid)) (pid : PeerId) :
    ErasesStatePrefix (stopPeerObservedWith timers pid)
      (stopPeerWith (fun pid => requireNotPending pid "wg_stop while a handshake is queued")
        purgeStagedPackets timersStop handshakeClear keypairsClear resetLastSentHandshake pid) := by
  apply stopPeerWith_erases
  · exact fun _ => erasesStatePrefix_lift _
  · exact fun _ => erasesStatePrefix_lift _
  · exact ht
  · exact fun _ => recordHelper_erases _ _ _
  · exact fun _ => erasesStatePrefix_lift _
  · exact fun _ => erasesStatePrefix_lift _

theorem stopObservedWith_erases (timers : PeerId → Obs Unit)
    (ht : ∀ pid, ErasesStatePrefix (timers pid) (timersStop pid)) :
    ErasesStatePrefix (stopObservedWith timers) WG.wgStop := by
  rw [stop_factor]
  exact stopWith_erases _ _ (stopPeerObservedWith_erases timers ht)

theorem downObservedWith_erases (timers : PeerId → Obs Unit)
    (ht : ∀ pid, ErasesStatePrefix (timers pid) (timersStop pid)) :
    ErasesStatePrefix (downObservedWith timers) WG.wgDown := by
  rw [down_factor]
  exact downWith_erases _ _ (stopObservedWith_erases timers ht)

theorem stopPeerObservedWith_preserves (entry : TagMap) (timers : PeerId → Obs Unit)
    (ht : ∀ pid, StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (timers pid))
    (keys : ∀ pid, SameView tagView (keypairsClear pid)) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (stopPeerObservedWith timers pid) := by
  apply stopPeerWith_preserves
  · intro pid
    exact pure_preserves entry ()
  · intro pid
    exact lift_frame entry _ (purgeStagedPackets_tag_frame pid)
  · exact ht
  · intro pid
    exact recordHelper_preserves entry (.handshakeClear pid) (fun _ => .cleared)
      (handshakeClear pid) rfl
  · intro pid
    exact lift_frame entry _ (keys pid)
  · intro pid
    exact lift_frame entry _ (resetLastSentHandshake_tag_frame pid)

theorem stopObservedWith_preserves (entry : TagMap) (timers : PeerId → Obs Unit)
    (ht : ∀ pid, StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (timers pid))
    (keys : ∀ pid, SameView tagView (keypairsClear pid)) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (stopObservedWith timers) := by
  apply stopWith_preserves
  · exact fun _ _ _ prior => prior.2
  · exact stopPeerObservedWith_preserves entry timers ht keys
  · exact lift_frame entry _ (store_frame getDev_sameWGStore)
  · intro b
    exact ambient_preserves entry (AmbientM.branch .stopPeersIter b)
  · exact ambient_preserves entry (AmbientM.unsupported _)
  · exact ambient_preserves entry (AmbientM.branch .stopDrainIter false)
  · exact lift_frame entry _ (modifyDev_frame _ (fun _ => rfl))
  · exact lift_frame entry _ (socket_frame (socketReinit_sameSocket none none))

theorem downObservedWith_preserves (entry : TagMap) (timers : PeerId → Obs Unit)
    (ht : ∀ pid, StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (timers pid))
    (keys : ∀ pid, SameView tagView (keypairsClear pid)) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (downObservedWith timers) :=
  downWith_preserves _ _ _ (stopObservedWith_preserves entry timers ht keys)
    (lift_frame entry _ (modifyDev_frame _ (fun _ => rfl)))

end Leanux.Proofs.WG.Noise.DriverTags.Control
