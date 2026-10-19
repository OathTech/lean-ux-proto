import Leanux.Proofs.WG.RetirementSecurity.ReadySocketComplete

/-! Actual cached head selection converts queued readiness to a local
conditional completion fact. The native CRYPTED branch discharges the
condition before completion can issue any socket receipt. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadySocket
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Completion ReadyCiphertext

def ReadyHead (items : List SkbId) (w : WGWorld) : Prop :=
  ∀first,items.head?=some first→TxDisposition.HeadState first .crypted w→Complete items w

def Guarded (items : List SkbId) (state : PacketState) (w : WGWorld) : Prop :=
  state=.crypted→Complete items w

theorem head_frame {a : WG.M α} (frame : SameView TxDisposition.txPackets a) : Preserves (ReadyHead items) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v final before run
  have cells:=(ProjectedAction.iff_run_ambient _ _ _).mp frame w ambient result v final run
  intro first head crypted
  have old:TxDisposition.HeadState first .crypted w:=by
    obtain ⟨p,stored,mark⟩:=crypted
    exact ⟨p,cells ▸ stored,mark⟩
  exact Complete.cells (before first head old) cells

theorem guarded_frame {a : WG.M α} (keeps : Preserves (Complete items) a) : Preserves (Guarded items state) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v final before run yes
  exact (hoare_iff_run_ambient _ _ _).mp keeps w ambient result v final (before yes) run

theorem access_spec {a : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix a native) (frame : Hoare native P Q) :
    PrefixEnsures (Inv P) Good (Completion.access a) (fun x h w=>Q x w.wg ∧ Good h) := by
  intro w h before
  obtain ⟨suffix,extension⟩:=Appends.focus Completion.Event.disposition Completion.disposition? (TxDisposition.nativeAccess a) w h
  have good:Good (runPrefix (Completion.access a) w h).2:=by
    unfold Good Completion.access
    rw [focusPrefix_other Completion.Event.disposition Completion.disposition? Completion.socket? (fun _=>rfl) _ w h]
    exact before.2
  refine ⟨suffix,extension,good,?_⟩
  cases result:(runPrefix (Completion.access a) w h).1 with
  | error stop=>trivial
  | ok out=>
    have nativeRun:=HolderPoll.native_receipt ((Completion.access_erases erases w h).symm.trans result)
    exact ⟨(hoare_iff_run_ambient _ _ _).mp frame w.wg _ out.1 out.2.wg _ before.1 nativeRun,good⟩

theorem branch_checked (decision : Decision) (value : Bool) :
    PrefixEnsures (Inv P) Good (liftPrefix (liftWG (Leanux.branch decision value)))
      (fun bit h w=>bit=value ∧ Inv P h w) := by
  apply PrefixEnsures.lift _ (fun _ _ before=>before.2)
  intro h w bit v before run
  cases run
  exact ⟨rfl,before⟩

theorem head_read (items : List SkbId) (id : SkbId) (head : items.head?=some id) :
    PrefixEnsures (Inv (ReadyHead items)) Good (Completion.access (getTxSkbPrefix id))
      (fun packet=>Inv (Guarded items packet.state)) := by
  apply access_spec (getTxSkbPrefix_erases id)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a packet v b before run
  obtain ⟨same,_,d,device,stored⟩:=Packets.getTxSkb_current id w v packet a b run
  subst v
  intro crypted
  exact before id head ⟨packet,by simp [TxDisposition.txPackets,device,stored],crypted⟩

theorem complete_retains (before : Complete items w)
    (cells : ∀id p,TxDisposition.txPackets v id=some p→TxDisposition.txPackets w id=some p) : Complete items v :=
  fun id member p found=>before id member p (cells id p found)

theorem free_complete (ids : List SkbId) : Preserves (Complete items) (TxDisposition.freeList ids) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have cells:=(hoare_iff_run_ambient _ _ _).mp (TxDisposition.freeList_wp ids (TxDisposition.txPackets w))
    w a result v b rfl run
  apply complete_retains before
  intro id p found
  rw [cells] at found
  dsimp only at found
  split at found
  · cases found
  · exact found

theorem dispose_guarded (peer : PeerId) (ids : List SkbId) (key : KeypairId) :
    Preserves (Guarded items state) (TxDisposition.disposeSource peer ids key) := by
  apply guarded_frame
  have factor:TxDisposition.disposeSource peer ids key=(do
      TxDisposition.freeList ids
      keypairPut (some key) false
      peerPut (some peer)
      pure true):=by simp [TxDisposition.disposeSource,TxDisposition.freeList]
  rw [factor]
  exact preserves_bind (free_complete ids) fun _=>
    preserves_bind (complete_frame (TxDisposition.keyPut_packets (some key) false)) fun _=>
    preserves_bind (complete_frame (TxDisposition.peerPut_packets (some peer))) fun _=>preserves_pure _

theorem drop_packets (peer : PeerId) :
    SameView TxDisposition.txPackets (do setPeer peer {(←getPeer peer) with txQueue:=(←getPeer peer).txQueue.dropPeeked}) := by
  apply SameView.bind (packets_peer peer)
  intro p
  apply SameView.bind (packets_peer peer)
  intro q
  unfold setPeer
  exact packets_modify _ (fun _=>rfl)

end Leanux.Proofs.WG.RetirementSecurity.ReadySocket
