import Leanux.Proofs.WG.TransmitSecurity.BatchJournalFinal
import Leanux.Proofs.WG.TransmitSecurity.CompletionReceipts

/-! Native TX completion retains the selected batch's peer/key fields.
Socket receipts are checked at their packet read, before later bookkeeping. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CompletionPeer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Completion

def Good (h : List Completion.Event) : Prop :=
  ∀ r ∈ h.filterMap Completion.socket?, r.packet.value.peer = r.pid

def Inv (pid : PeerId) (slot : KeypairId) (items : List SkbId)
    (h : List Completion.Event) (w : World) : Prop :=
  BatchCoherence.Aligned w.wg pid slot items ∧ Good h

theorem quiet {g : PrefixM Completion.Event α} {a : Leanux.M α}
    (appends : Appends g) (history : HistoryFrame Completion.socket? g)
    (erases : ErasesPrefix g a)
    (frame : Preserves (fun w : World => BatchCoherence.Aligned w.wg pid slot items) a) :
    PrefixPreserves (Inv pid slot items) Good g := by
  intro w h before
  obtain ⟨suffix,extension⟩ := appends w h
  have good : Good (runPrefix g w h).2 := by
    unfold Good
    rw [history w h]
    exact before.2
  refine ⟨suffix,extension,good,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    exact ⟨(hoare_iff_run _ _ _).mp frame w out.1 out.2 before.1 ((erases w h).symm.trans result),good⟩

theorem access {a : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix a native) (frame : SameView PacketMaterial.view native) :
    PrefixPreserves (Inv pid slot items) Good (Completion.access a) :=
  quiet (Appends.focus _ _ _)
    (focusPrefix_other _ _ _ (fun _ => rfl) _)
    (Completion.access_erases erases)
    (PublicationPoll.native_product _ _ (BatchCoherence.aligned frame))

theorem lift_safe (a : Leanux.M α)
    (frame : Preserves (fun w : World => BatchCoherence.Aligned w.wg pid slot items) a) :
    PrefixPreserves (Inv pid slot items) Good (liftPrefix a) :=
  quiet (Appends.lift a) (HistoryFrame.lift _ a) (erasesPrefix_lift a) frame

theorem ambient (a : AmbientM α) :
    PrefixPreserves (Inv pid slot items) Good (liftPrefix (monadLift a : Leanux.M α)) :=
  lift_safe _ (productAmbient_spec a _ (fun _ _ hi => hi))

theorem disposition (e : TxDisposition.Event) :
    PrefixPreserves (Inv pid slot items) Good (emitPrefix (.disposition e)) := by
  intro w h before
  have good : Good (h ++ [.disposition e]) := by
    simpa only [Good,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      Completion.socket?,List.append_nil] using before.2
  exact ⟨[.disposition e],rfl,good,before.1,good⟩

theorem wire {a : WG.M α} (frame : SameView txCryptWire a) : SameView PacketMaterial.view a :=
  PacketMaterial.of_packets (frame.factor Prod.snd)

theorem peer_modify (pid : PeerId) (f : Peer → Peer) :
    SameView PacketMaterial.view (do setPeer pid (f (← getPeer pid))) := by
  apply SameView.bind (PacketMaterial.read_peer pid)
  intro p
  unfold setPeer
  exact PacketMaterial.modify_device _ (fun _ => rfl)

theorem send4 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView PacketMaterial.view (WG.send4 e cache bytes ds exactRx) :=
  wire ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send4_cryptWire) e cache bytes ds exactRx)

theorem send6 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView PacketMaterial.view (WG.send6 e cache bytes ds exactRx) :=
  wire ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send6_cryptWire) e cache bytes ds exactRx)

theorem authenticated_sent (pid : PeerId) :
    SameView PacketMaterial.view (timersAnyAuthenticatedPacketSent pid) := by
  unfold timersAnyAuthenticatedPacketSent
  exact wire (delTimer_cryptWire pid .sendKeepalive)

theorem branch (decision : Decision) (value : Bool) :
    PrefixPreserves (Inv pid slot items) Good (liftPrefix (liftWG (Leanux.branch decision value))) := by
  apply lift_safe
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run
  exact before

end Leanux.Proofs.WG.TransmitSecurity.CompletionPeer
