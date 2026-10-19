import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialNativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayHistory

/-! Positional replay certificates carry the actual decrypting allocation.
They are attached at the indexed native counter call, before confirmation. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Replay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {h suffix : List E}

def Certified (history : List TransportDriver.OriginEvent) (r : TransportDriver.Replay) : Prop :=
  r.Valid ∧ r.Selected ∧ ∃ core, Certificate history r.skb r.packet r.run.before.wg core ∧
    ∀ current, pool r.run.before.wg r.packet.keypair = some current → current = core

def Checked (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (pre : List E) (event : E) : Prop :=
  ∀ r, replay event = some r → Certified (pre.filterMap origin) r

def Safe (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (history : List E) : Prop :=
  ∀ pre event post, history = pre ++ event :: post → Checked origin replay pre event

def Inv (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (history : List E) (w : World) : Prop :=
  ReceiveMaterial.Inv (history.filterMap origin) w.wg ∧ Safe origin replay history

def Picked (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (skb : SkbId) (pkt : RxPacket)
    (h : List E) (w : World) : Prop :=
  Inv origin replay h w ∧ (RxDisposition.nativeRxStore w.wg).2 skb = some pkt

theorem Certified.authenticated (certified : Certified history r) : TransportReplay.Certified history r :=
  ⟨certified.1,certified.2.1,certified.2.2.choose_spec.1.authenticated⟩

theorem Safe.append (hi : Safe origin replay h)
    (next : ∀ pre event post, suffix = pre ++ event :: post → Checked origin replay (h ++ pre) event) :
    Safe origin replay (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    (Checked origin replay) h suffix hi next

theorem Safe.quiet (hi : Safe origin replay h) (quiet : suffix.filterMap replay = []) :
    Safe origin replay (h ++ suffix) := by
  apply hi.append
  intro pre event post position r recorded
  have member : event ∈ suffix := by rw [position]; simp
  have found := List.mem_filterMap.mpr ⟨event,member,recorded⟩
  rw [quiet] at found
  cases found

theorem counter_checked (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (skb : SkbId) (pkt : RxPacket) (crypted : pkt.state = .crypted) :
    PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay)
      (TransportDriver.counter record skb pkt) (fun _ => Inv origin replay) := by
  intro w h hi
  rw [TransportDriver.counter_run]
  cases run : (liftWG (counterValidate pkt.keypair pkt.nonce)).run w with
  | error err => exact ⟨[],by simp,hi.1.2,True.intro⟩
  | ok out =>
    rcases out with ⟨value,v⟩
    let receipt : TransportDriver.Replay := ⟨skb,pkt,⟨value,w,v⟩⟩
    obtain ⟨d,device,cell⟩ := Option.bind_eq_some_iff.mp hi.2
    obtain ⟨_,core,certificate,conditional⟩ := hi.1.1 d device skb pkt cell crypted
    have certified : Certified (h.filterMap origin) receipt :=
      ⟨run,⟨hi.2,crypted⟩,core,certificate,conditional⟩
    have safe : Safe origin replay (h ++ [record receipt]) := by
      apply hi.1.2.append
      intro pre event post position r recorded
      cases pre with
      | nil =>
        cases position
        have eq : receipt = r := Option.some.inj ((inverse receipt).symm.trans recorded)
        subst r
        simpa only [List.append_nil] using certified
      | cons x xs =>
        have lengths := congrArg List.length position
        simp only [List.length_append,List.length_cons,List.length_nil] at lengths
        omega
    have kept := (hoare_iff_run _ _ _).mp
      (PublicationPoll.native_product _ _ (ReceiveMaterial.counter pkt.keypair pkt.nonce))
      w value v hi.1.1 run
    refine ⟨[record receipt],rfl,safe,?_,safe⟩
    simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
      Option.toList_none,List.nil_append,List.append_nil] using kept

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Replay
