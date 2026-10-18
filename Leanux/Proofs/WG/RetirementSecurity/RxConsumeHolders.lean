import Leanux.Proofs.WG.RetirementSecurity.RxRefusalHolders

/-! Full original consumeData transports the concrete key-holder account.
The only structural input beyond that account is campaign 1's packet
frontier invariant, used at the actual newRxSkb allocation. Lookup borrowing,
key acquisition, queue publication and refusal cleanup are derived inside
this caller rather than supplied as boundary invariants. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem HolderAccount.consume_data (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (a b : Ambient)
    (run : ((consumeData msg src ds).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  rw [← RxOrigin.consumeSource_eq] at run
  simp only [RxOrigin.consumeSource,RxOrigin.consumeWith,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨admission,u,c,admitRun,tail⟩ := run
  cases admission with
  | none =>
    cases tail
    exact account.admit_none msg src ds a b admitRun
  | some ctx =>
    obtain ⟨allocation,key,hu,detached,packet,ready,p,peer⟩ :=
      account.admitted_rx bounded msg src ds a c admitRun
    obtain ⟨d,device,stored⟩ := Option.bind_eq_some_iff.mp packet
    have storedPeer : d.peers[ctx.packet.peer]? = some p := by
      simpa [peerAt,device] using peer
    have resident : ∃ k, keyAt u allocation.slot = some k ∧ k.internalId = allocation.stamp := by
      obtain ⟨loans,_,credits⟩ := hu
      obtain ⟨k,found,stamp,_⟩ := credits.resident (allocation := allocation) (by simp)
      exact ⟨k,found,stamp⟩
    obtain ⟨k,found,stamp⟩ := resident
    have loan : receiveLoan u ctx.packet.peer ctx.slot =
        some ⟨.receive ctx.packet.peer ctx.slot,allocation⟩ := by
      have named : nameLoan u (.receive ctx.packet.peer ctx.slot) allocation.slot =
          some ⟨.receive ctx.packet.peer ctx.slot,allocation⟩ := by
        cases allocation
        simp [nameLoan,found,stamp]
      simpa [receiveLoan,packet,←key] using named
    exact hu.finish_rx ctx device stored storedPeer loan key.symm detached ready c b tail

end Leanux.Proofs.WG.RetirementSecurity
