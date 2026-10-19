import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
import Leanux.Proofs.WG.TransmitSecurity.PacketPayloadFrames

/-! Native CRYPTED publication follows successful byte installation for
every member. Failure breaks the walk and publishes DEAD instead. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues

theorem Complete.payload (before : Complete items w)
    (same : TransmitSecurity.PacketPayload.view v=TransmitSecurity.PacketPayload.view w) : Complete items v := by
  intro id member p resident
  have cell:=congrFun same id
  simp only [TransmitSecurity.PacketPayload.view,resident,Option.map_some] at cell
  obtain ⟨old,found,eq⟩:=Option.map_eq_some_iff.mp cell.symm
  have bytes:old.bytes=p.bytes:=by
    simpa only [TransmitSecurity.PacketPayload.material] using congrArg DataPacket.bytes eq
  exact bytes ▸ before id member old found

theorem published (items : List SkbId) (first : SkbId) (head : items.head?=some first)
    (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerTx items state).run w).run a=.ok (((),v),b))
    (crypted : TxDisposition.HeadState first .crypted v) : state=.crypted := by
  cases items with
  | nil=>cases head
  | cons id rest=>
    cases head
    obtain ⟨p,resident,mark⟩:=(hoare_iff_run_ambient _ _ _).mp (TxDisposition.publication_head first rest state)
      w a () v b True.intro run
    obtain ⟨q,found,done⟩:=crypted
    have same:p=q:=Option.some.inj (resident.symm.trans found)
    exact mark.symm.trans (same ▸ done)

theorem source (items : List SkbId) (first : SkbId) (head : items.head?=some first) :
    RxWorkers.encryptStepTailSource (some items)=(do
      _←branch .encWorkerConsumed true
      let saved←getTxSkb first
      let state←forIn items PacketState.crypted (body saved.keypair)
      if state==.crypted then _←branch .encWorkerSkbIterate false
      enqueuePerPeerTx items state
      return true : Leanux.M Bool) := by
  simp only [RxWorkers.encryptStepTailSource,head]
  rfl

/-- No physical separation premise is needed for this one selected tail:
even repeated IDs are nonempty after complete successful traversal. Global
queue transport additionally needs the initialized ownership carrier. -/
theorem native_tail (items : List SkbId) (first : SkbId) (head : items.head?=some first)
    (run : (RxWorkers.encryptStepTailSource (some items)).run w=.ok (result,v))
    (crypted : TxDisposition.HeadState first .crypted v.wg) : Complete items v.wg := by
  rw [source items first head] at run
  simp only [MaterialOrigin.bind_ok] at run
  obtain ⟨_,u,consumed,saved,t,read,state,s,loop,tail⟩:=run
  have finish (z : World)
      (same:z.wg=s.wg)
      (tail : (do enqueuePerPeerTx items state; pure true : Leanux.M Bool).run z=.ok (result,v)) :
      Complete items v.wg := by
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨_,last,publish,returned⟩:=tail
    cases returned
    have native:=HolderPoll.native_receipt publish
    have done:=published items first head state _ _ native crypted
    have all:=loop_complete items saved.keypair .crypted (by simpa only [done] using loop)
    have payload:TransmitSecurity.PacketPayload.view v.wg=TransmitSecurity.PacketPayload.view z.wg:=
      (ProjectedAction.iff_run_ambient _ _ _).mp (TransmitSecurity.PacketPayload.publish items state)
        z.wg _ () v.wg _ native
    exact (same ▸ all).payload payload
  split at tail
  · rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨_,z,step,tail⟩:=tail
    have same:z.wg=s.wg:=by cases step; rfl
    exact finish z same tail
  · exact finish s rfl tail

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
