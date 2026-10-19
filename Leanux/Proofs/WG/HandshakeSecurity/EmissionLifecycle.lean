import Leanux.Proofs.WG.HandshakeSecurity.EmissionClearing
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeLifecycleSource

/-! Device creation and the post-drain destruction suffix preserve the
pending sent buffer. Whole shutdown/deletion are composed separately around
their real send-work drain callbacks. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.EmissionLifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open AuthenticatedEffects TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem ratelimiter_init : SameView WGWorld.sent ratelimiterInit := by
  sent_frame [ratelimiterInit] using []

theorem ratelimiter_init_spec (P : List SentDatagram → Prop) :
    Preserves (fun w => P w.sent) ratelimiterInit := ratelimiter_init.wp P

theorem garbage_collect (work : Bool) : SameView WGWorld.sent (gcEntries work) := by
  sent_frame [gcEntries,hiddenClock] using [EmissionDump.list_spec,EmissionDump.range_spec]

theorem garbage_collect_spec (P : List SentDatagram → Prop) (work : Bool) :
    Preserves (fun w => P w.sent) (gcEntries work) := (garbage_collect work).wp P

theorem ratelimiter_uninit : SameView WGWorld.sent ratelimiterUninit := by
  sent_frame [ratelimiterUninit,mayHaveSlept] using [garbage_collect_spec]

theorem ratelimiter_uninit_spec (P : List SentDatagram → Prop) :
    Preserves (fun w => P w.sent) ratelimiterUninit := ratelimiter_uninit.wp P

theorem cookie_init : SameView WGWorld.sent cookieCheckerInit := by
  sent_frame [cookieCheckerInit] using []

theorem cookie_init_spec (P : List SentDatagram → Prop) :
    Preserves (fun w => P w.sent) cookieCheckerInit := cookie_init.wp P

theorem pubkey_allocate : SameView WGWorld.sent pubkeyHashtableAlloc := by
  sent_frame [pubkeyHashtableAlloc,envOk] using []

theorem pubkey_allocate_spec (P : List SentDatagram → Prop) :
    Preserves (fun w => P w.sent) pubkeyHashtableAlloc := pubkey_allocate.wp P

theorem newlink : SameView WGWorld.sent wgNewlink := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold wgNewlink
  simp (config := {zeta := false}) only [envOk,mayHaveSlept,skipCutExactly,skipCut,branch,unsupported]
  repeat' first
    | (cookie_source_head cookieCheckerInit; exact cookie_init_spec (fun s => s = initial))
    | (cookie_source_head pubkeyHashtableAlloc; exact pubkey_allocate_spec (fun s => s = initial))
    | (cookie_source_head ratelimiterInit; exact ratelimiter_init_spec (fun s => s = initial))
    | consumer_sent_step initial

theorem newlink_spec (P : List SentDatagram → Prop) :
    Preserves (fun w => P w.sent) wgNewlink := newlink.wp P

theorem create : SameView WGWorld.sent wgCreate := by
  sent_frame [wgCreate,wgSetup] using [newlink_spec]

theorem destruct_finish : SameView WGWorld.sent
    (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish) := by
  sent_frame [_private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish,
    retireDeviceUnits,modifyAmbient,mayHaveSlept] using [ratelimiter_uninit_spec]

end Leanux.Proofs.WG.HandshakeSecurity.EmissionLifecycle
