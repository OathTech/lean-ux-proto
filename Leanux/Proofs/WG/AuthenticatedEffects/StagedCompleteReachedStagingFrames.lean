import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingSource

/-! Static packet-shape facts are carried beside the same native selected
carrier. These logical frames do not infer a reached world from an error. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal

theorem with_fact {Safe : List Event→Prop}
    (rule : StatePrefixPreserves P Safe action) (fact : Prop) :
    StatePrefixPreserves (fun h w a=>P h w a ∧ fact) Safe action := by
  intro w a h before
  obtain ⟨suffix,extended,safe,post⟩:=rule w a h before.1
  refine ⟨suffix,extended,safe,?_⟩
  cases result : (runPrefix (action.run w) a h).1 with
  | error stop=>trivial
  | ok out=>exact ⟨by simpa only [result] using post,before.2⟩

theorem shape_snoc (before : BatchPayload.Shape pid kid seen packets) (packet : Packet)
    (nonce ds : Nat) :
    BatchPayload.Shape pid kid (seen++[packet])
      (packets++[{peer:=pid,keypair:=kid,nonce,plaintext:=packet,ds}]) := by
  refine ⟨?_,?_⟩
  · simp only [List.map_append,List.map_cons,List.map_nil]
    exact congrArg (fun xs=>xs++[packet]) before.1
  · intro input member
    rcases List.mem_append.mp member with old|new
    · exact before.2 input old
    · have same : input=DataPacket.mk pid kid nonce packet ds .uncrypted [] := by simpa using new
      subst input
      exact ⟨rfl,rfl⟩

theorem normal {Safe : List Event→Prop} {action : WGPrefix Event α}
    (rule : StatePrefixEnsures P Safe action Q) (before : P h w a)
    (run : runWGPrefix action w a h=(.ok ((value,v),b),last)) : Q value last v b := by
  obtain ⟨_,_,_,post⟩:=rule w a h before
  change runPrefix (action.run w) a h=_ at run
  rw [run] at post
  exact post

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
