import Leanux.Proofs.WG.AuthenticatedEffects.ReplyObservation

/-! Observation of actual cookie datagrams, with native construction, exact
width and source binding. The continuous MAC/load witness locates this suffix
inside either qualifying original handshake receive. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

def cookieEmitted (msg : List UInt8) (src : SkbSource) : WGPrefix DatagramReceipt Unit := do
  let bytes ← liftWGPrefix (cookieMessageCreate (u32le msg 4) src
    ((msg.drop (msg.length - 32)).take 16))
  replyEmitted src bytes

theorem cookieEmitted_erases (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (cookieEmitted msg src) (sendHandshakeCookie msg src) :=
  erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => replyEmitted_erases _ _)

theorem cookieEmitted_receipts (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (h : List DatagramReceipt) :
    ∃ suffix, (runWGPrefix (cookieEmitted msg src) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix,
        r.Valid ∧ r.endpoint.addr = src.saddr ∧ r.endpoint.port = src.sport ∧
        r.bytes.length = 64 ∧ r.ds = 0 := by
  unfold cookieEmitted
  rw [liftWG_bind_run]
  cases created : ((cookieMessageCreate (u32le msg 4) src
      ((msg.drop (msg.length - 32)).take 16)).run w).run a with
  | error err => exact ⟨[],by simp⟩
  | ok out =>
    rcases out with ⟨⟨bytes,u⟩,b⟩
    have width := cookieMessageCreate_length _ src _ w u a b bytes created
    obtain ⟨suffix,eq,len,members⟩ := replyEmitted_receipts src bytes u b h
    refine ⟨suffix,eq,len,?_⟩
    intro r mem
    obtain ⟨valid,addr,port,data,ds⟩ := members r mem
    exact ⟨valid,addr,port,by simpa only [data] using width,ds⟩

theorem qualifying_cookie_observer_erases (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (path : Cookies.FailedMac2 msg src w a) (h : List DatagramReceipt) :
    (runWGPrefix (cookieEmitted msg src) path.made (cookieReplyEntry msg path.checked) h).1 =
      ((receiveHandshakePacket msg src).run w).run a := by
  rw [qualifying_rejected_run msg src w a kind path]
  exact cookieEmitted_erases msg src _ _ _

theorem cookieEmitted_later_stop (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient) (before after : List DatagramReceipt) (err : Stop)
    (run : runWGPrefix (cookieEmitted msg src) w a before = (.ok (((),v),b),after)) :
    runWGPrefix (cookieEmitted msg src >>= fun _ => (throw err : WGPrefix DatagramReceipt Unit))
      w a before = (.error err,after) := by
  change runStatePrefix _ w a before = _
  rw [runStatePrefix_bind]
  change runStatePrefix _ w a before = _ at run
  rw [run]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects
