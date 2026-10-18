import Leanux.Proofs.WG.RetirementSecurity.TxStagingFundingFrames

/-! The actual nonce loop retains the acquired key credit until either its
original rejection pays it or its finished packet batch is submitted. Every
constructed packet carries the same acquired key slot. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

namespace StagingFunding

def Borrowed (allocation : Credits.Allocation) (pid : PeerId) (temporary : Credits.Ledger)
    (w : WGWorld) : Prop :=
  HolderAccount (allocation :: temporary) w ∧ Packets.Inv w ∧ KeyCompatible pid allocation.slot w

def reserveSource (kid : KeypairId) : WG.M Nat := do
  let k ← getKeypair kid
  setKeypair kid {k with sendingCounter := k.sendingCounter + 1}
  pure k.sendingCounter

theorem reserve_borrowed (allocation : Credits.Allocation) (pid : PeerId) (temporary : Credits.Ledger) :
    Preserves (Borrowed allocation pid temporary) (reserveSource allocation.slot) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  simp only [reserveSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨k,u,c,readRun,_,t,e,setRun,done⟩ := run
  obtain ⟨same,clock,d,device,stored⟩ := KeyTimes.getKeypair_return allocation.slot w u k a c readRun
  subst u
  subst c
  cases done
  have account := (hoare_iff_run_ambient _ _ _).mp
    (key_update_holders allocation.slot (fun k => {k with sendingCounter := k.sendingCounter + 1})
      (fun _ => rfl) (fun _ => rfl) (allocation :: temporary)) w a () v b before.1
    (by rw [MaterialOrigin.bind_ok_ambient]; exact ⟨k,w,a,readRun,setRun⟩)
  have after : {w with dev := some {d with keypairs := d.keypairs.insert allocation.slot {k with sendingCounter := k.sendingCounter + 1}}} = v ∧ a = b := by
    simpa [setKeypair,modifyDev,device] using setRun
  refine ⟨account,?_,?_⟩
  · rw [← after.1]
    simpa only [Packets.Inv,Packets.snapshot,Packets.deviceStore,device] using before.2.1
  · intro current key currentDevice currentKey
    rw [← after.1] at currentDevice
    cases currentDevice
    simp only [Std.TreeMap.getElem?_insert_self] at currentKey
    cases currentKey
    exact before.2.2 d k device stored

abbrev Accumulator := Option Unit × List DataPacket

def body (pid kid : Nat) (packets : List WG.Packet) (pkt : WG.Packet)
    (state : Accumulator) : WG.M (ForInStep Accumulator) := do
  _ ← branch .stagedNonceIterate true
  let ds ← ipTunnelEcnEncap pkt
  let nonce ← reserveSource kid
  if ← branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES then
    let stopped ← stagedOutNokey pid packets (some kid) true
    return .done (some stopped,state.2)
  return .yield (none,state.2 ++ [{peer := pid,keypair := kid,nonce,plaintext := pkt,ds}])

def LoopResult (allocation : Credits.Allocation) (pid : PeerId) (temporary : Credits.Ledger)
    (state : Accumulator) (w : WGWorld) : Prop :=
  match state.1 with
  | some _ => HolderAccount temporary w
  | none => Borrowed allocation pid temporary w ∧ ∀ packet ∈ state.2, packet.keypair = allocation.slot

theorem body_funding (before : Borrowed allocation pid temporary w)
    (keys : ∀ packet ∈ accumulated, packet.keypair = allocation.slot)
    (packets : List WG.Packet) (pkt : WG.Packet) (a b : Ambient)
    (run : ((body pid allocation.slot packets pkt (none,accumulated)).run w).run a =
      .ok ((result,v),b)) :
    match result with
    | .done state => state.1.isSome ∧ LoopResult allocation pid temporary state v
    | .yield state => state.1 = none ∧ LoopResult allocation pid temporary state v := by
  simp only [body,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,branchRun,ds,t,e,ecnRun,nonce,s,f,reserveRun,rejected,r,g,testRun,tail⟩ := run
  have same : u = w := by cases branchRun; rfl
  subst u
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (ipTunnelEcnEncap_sameWGWorld pkt)
    w c ds t e ecnRun
  change t = w at same
  subst t
  have reserved := (hoare_iff_run_ambient _ _ _).mp (reserve_borrowed allocation pid temporary)
    w e nonce s f before reserveRun
  have same : r = s := by cases testRun; rfl
  subst r
  cases rejected with
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨stopped,t,e,rejectRun,done⟩ := tail
    cases stopped
    cases done
    exact ⟨rfl,HolderAccount.no_key (some allocation) reserved.1 pid packets true g b rejectRun⟩
  | false =>
    simp only [Bool.false_eq_true,ite_false] at tail
    cases tail
    refine ⟨rfl,reserved,?_⟩
    intro packet member
    rcases List.mem_append.mp member with old | fresh
    · exact keys packet old
    · exact congrArg DataPacket.keypair (List.mem_singleton.mp fresh)

theorem loop_funding (remaining : List WG.Packet) (before : Borrowed allocation pid temporary w)
    (keys : ∀ packet ∈ accumulated, packet.keypair = allocation.slot)
    (packets : List WG.Packet) (a b : Ambient)
    (run : ((forIn remaining (none,accumulated) (body pid allocation.slot packets)).run w).run a =
      .ok ((state,v),b)) : LoopResult allocation pid temporary state v := by
  induction remaining generalizing w a b accumulated state v with
  | nil => simp only [List.forIn_nil] at run; cases run; exact ⟨before,keys⟩
  | cons pkt rest ih =>
    rw [List.forIn_cons,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨result,u,c,bodyRun,tail⟩ := run
    have funded := body_funding before keys packets pkt a c bodyRun
    cases result with
    | done next => cases tail; exact funded.2
    | yield next =>
      obtain ⟨flag,funded⟩ := funded
      obtain ⟨option,acc⟩ := next
      simp only at flag
      subst option
      exact ih funded.1 funded.2 c b tail

end StagingFunding
end Leanux.Proofs.WG.RetirementSecurity
