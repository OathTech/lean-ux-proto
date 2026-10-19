import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeInitialized
import Leanux.Proofs.WG.TransmitSecurity.CompletionReceipts

/-! Socket readiness is checked at the actual packet read. The local source
carrier retains complete packet cells and emits only nonempty-byte receipts. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadySocket
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Completion ReadyCiphertext
variable {id : SkbId}

def Good (h : List Completion.Event) : Prop :=
  ∀r∈h.filterMap Completion.socket?,r.packet.value.bytes≠[]

def Inv (P : WGWorld→Prop) (h : List Completion.Event) (w : World) : Prop := P w.wg ∧ Good h

theorem quiet {g : PrefixM Completion.Event α} {a : Leanux.M α}
    (appends : Appends g) (history : HistoryFrame Completion.socket? g)
    (erases : ErasesPrefix g a) (frame : Preserves (fun w : World=>P w.wg) a) :
    PrefixPreserves (Inv P) Good g := by
  intro w h before
  obtain ⟨suffix,extension⟩:=appends w h
  have good : Good (runPrefix g w h).2:=by unfold Good; rw [history w h]; exact before.2
  refine ⟨suffix,extension,good,?_⟩
  cases result:(runPrefix g w h).1 with
  | error stop=>trivial
  | ok out=>exact ⟨(hoare_iff_run _ _ _).mp frame w out.1 out.2 before.1 ((erases w h).symm.trans result),good⟩

theorem access {a : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix a native) (frame : Preserves P native) :
    PrefixPreserves (Inv P) Good (Completion.access a) :=
  quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _=>rfl) _)
    (Completion.access_erases erases) (PublicationPoll.native_product _ _ frame)

theorem lift_safe (a : Leanux.M α) (frame : Preserves (fun w : World=>P w.wg) a) :
    PrefixPreserves (Inv P) Good (liftPrefix a) :=
  quiet (Appends.lift a) (HistoryFrame.lift _ a) (erasesPrefix_lift a) frame

theorem ambient (a : AmbientM α) : PrefixPreserves (Inv P) Good (liftPrefix (monadLift a : Leanux.M α)) :=
  lift_safe _ (productAmbient_spec a _ (fun _ _ before=>before))

theorem disposition (e : TxDisposition.Event) : PrefixPreserves (Inv P) Good (emitPrefix (.disposition e)) := by
  intro w h before
  have good : Good (h++[.disposition e]):=by
    simpa only [Good,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,Completion.socket?,List.append_nil] using before.2
  exact ⟨[.disposition e],rfl,good,before.1,good⟩

theorem branch (decision : Decision) (value : Bool) :
    PrefixPreserves (Inv P) Good (liftPrefix (liftWG (Leanux.branch decision value))) := by
  apply lift_safe
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run
  exact before

theorem Complete.cells (before : Complete items w) (same : TxDisposition.txPackets v=TxDisposition.txPackets w) :
    Complete items v:=fun id member=>(before id member).frame (congrFun same id)

theorem complete_frame {a : WG.M α} (frame : SameView TxDisposition.txPackets a) : Preserves (Complete items) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v final before run
  exact Complete.cells before ((ProjectedAction.iff_run_ambient _ _ _).mp frame w ambient result v final run)

theorem packets_read (id : SkbId) : SameView TxDisposition.txPackets (getTxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a packet v b run
  exact congrArg TxDisposition.txPackets (Packets.getTxSkb_current id w v packet a b run).1

theorem packets_peer (pid : PeerId) : SameView TxDisposition.txPackets (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg TxDisposition.txPackets (Peers.getPeer_current pid w v p a b run).1

theorem packets_modify (f : Device→Device) (same : ∀d,(f d).txSkbs=d.txSkbs) :
    SameView TxDisposition.txPackets (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  funext id
  simp [TxDisposition.txPackets,Option.bind_map,Function.comp_def,same]

theorem peer_modify (pid : PeerId) (f : Peer→Peer) :
    SameView TxDisposition.txPackets (do setPeer pid (f (←getPeer pid))) := by
  apply SameView.bind (packets_peer pid)
  intro p
  unfold setPeer
  exact packets_modify _ (fun _=>rfl)

theorem wire {a : WG.M α} (frame : SameView txCryptWire a) : Preserves (Complete items) a :=
  complete_frame (frame.factor Prod.snd)

theorem send4 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Preserves (Complete items) (WG.send4 e cache bytes ds exactRx) :=
  wire ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send4_cryptWire) e cache bytes ds exactRx)

theorem send6 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Preserves (Complete items) (WG.send6 e cache bytes ds exactRx) :=
  wire ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send6_cryptWire) e cache bytes ds exactRx)

theorem authenticated_sent (pid : PeerId) : Preserves (Complete items) (timersAnyAuthenticatedPacketSent pid) := by
  unfold timersAnyAuthenticatedPacketSent
  exact wire (delTimer_cryptWire pid .sendKeepalive)

theorem read_cell (r : RunWitness DataPacket) (valid : r.Valid (liftWG (getTxSkb id))) :
    r.after.wg=r.before.wg ∧ TxDisposition.txPackets r.after.wg id=some r.value := by
  change (liftWG (getTxSkb id)).run r.before=.ok (r.value,r.after) at valid
  rw [liftWG_run] at valid
  cases native:((getTxSkb id).run r.before.wg).run r.before.ambient with
  | error stop=>simp [native,Except.map] at valid
  | ok out=>
    obtain ⟨⟨packet,w⟩,a⟩:=out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
    obtain ⟨same,world⟩:=valid
    obtain ⟨kept,_,d,device,resident⟩:=Packets.getTxSkb_current id r.before.wg w packet r.before.ambient a native
    have worldEq:r.after.wg=w:=congrArg World.wg world.symm
    refine ⟨worldEq.trans kept,?_⟩
    rw [worldEq,kept]
    simp [TxDisposition.txPackets,device,resident,same]

end Leanux.Proofs.WG.RetirementSecurity.ReadySocket
