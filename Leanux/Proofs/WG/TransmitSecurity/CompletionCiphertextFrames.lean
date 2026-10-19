import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginWorker
import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginStagingFrames
import Leanux.Proofs.WG.TransmitSecurity.CompletionReceipts

/-! Completion frames retain resident ciphertext certificates. Packet reads
will transfer those certificates to actual socket receipts before disposal. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CompletionCiphertext
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Completion

def ReadOrigin (bank : List WorkerEncryption.Receipt) (id : SkbId)
    (read : RunWitness DataPacket) : Prop :=
  ∀ generation, PacketOrigins.epoch read.before.wg = some generation →
    read.value.bytes ≠ [] →
      CiphertextOrigins.Certificate bank generation id (PacketPayload.material read.value)

def Good (bank : List WorkerEncryption.Receipt) (h : List Completion.Event) : Prop :=
  ∀ r ∈ h.filterMap Completion.socket?, ReadOrigin bank r.id r.packet

def Inv (bank : List WorkerEncryption.Receipt) (h : List Completion.Event) (w : World) : Prop :=
  CiphertextOrigins.Inv bank w.wg ∧ Good bank h

theorem quiet {g : PrefixM Completion.Event α} {a : Leanux.M α}
    (appends : Appends g) (history : HistoryFrame Completion.socket? g)
    (erases : ErasesPrefix g a)
    (frame : Preserves (fun w : World => CiphertextOrigins.Inv bank w.wg) a) :
    PrefixPreserves (Inv bank) (Good bank) g := by
  intro w h before
  obtain ⟨suffix,extension⟩ := appends w h
  have good : Good bank (runPrefix g w h).2 := by
    unfold Good
    rw [history w h]
    exact before.2
  refine ⟨suffix,extension,good,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    exact ⟨(hoare_iff_run _ _ _).mp frame w out.1 out.2 before.1 ((erases w h).symm.trans result),good⟩

theorem access {a : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix a native) (frame : Preserves (CiphertextOrigins.Inv bank) native) :
    PrefixPreserves (Inv bank) (Good bank) (Completion.access a) :=
  quiet (Appends.focus _ _ _)
    (focusPrefix_other _ _ _ (fun _ => rfl) _)
    (Completion.access_erases erases)
    (PublicationPoll.native_product _ _ frame)

theorem lift_safe (a : Leanux.M α)
    (frame : Preserves (fun w : World => CiphertextOrigins.Inv bank w.wg) a) :
    PrefixPreserves (Inv bank) (Good bank) (liftPrefix a) :=
  quiet (Appends.lift a) (HistoryFrame.lift _ a) (erasesPrefix_lift a) frame

theorem ambient (a : AmbientM α) :
    PrefixPreserves (Inv bank) (Good bank) (liftPrefix (monadLift a : Leanux.M α)) :=
  lift_safe _ (productAmbient_spec a _ (fun _ _ hi => hi))

theorem disposition (e : TxDisposition.Event) :
    PrefixPreserves (Inv bank) (Good bank) (emitPrefix (.disposition e)) := by
  intro w h before
  have good : Good bank (h ++ [.disposition e]) := by
    simpa only [Good,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      Completion.socket?,List.append_nil] using before.2
  exact ⟨[.disposition e],rfl,good,before.1,good⟩

theorem wire {a : WG.M α} (kept : SameView txCryptWire a) :
    Preserves (CiphertextOrigins.Inv bank) a :=
  CiphertextOrigins.frame (CiphertextOrigins.snapshot_wire kept)

theorem peer_modify (pid : PeerId) (f : Peer → Peer) :
    Preserves (CiphertextOrigins.Inv bank) (do setPeer pid (f (← getPeer pid))) :=
  preserves_bind (CiphertextOrigins.NativeFrames.read_peer pid) (fun _ =>
    CiphertextOrigins.frame (CiphertextOrigins.modify _ (fun _ => rfl) (fun _ => rfl)))

theorem send4 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Preserves (CiphertextOrigins.Inv bank) (WG.send4 e cache bytes ds exactRx) :=
  wire ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send4_cryptWire) e cache bytes ds exactRx)

theorem send6 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Preserves (CiphertextOrigins.Inv bank) (WG.send6 e cache bytes ds exactRx) :=
  wire ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send6_cryptWire) e cache bytes ds exactRx)

theorem authenticated_sent (pid : PeerId) :
    Preserves (CiphertextOrigins.Inv bank) (timersAnyAuthenticatedPacketSent pid) := by
  unfold timersAnyAuthenticatedPacketSent
  exact wire (delTimer_cryptWire pid .sendKeepalive)

theorem branch (decision : Decision) (value : Bool) :
    PrefixPreserves (Inv bank) (Good bank) (liftPrefix (liftWG (Leanux.branch decision value))) := by
  apply lift_safe
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run
  exact before

end Leanux.Proofs.WG.TransmitSecurity.CompletionCiphertext
