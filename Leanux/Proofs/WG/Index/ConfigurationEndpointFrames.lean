import Leanux.Proofs.WG.Index.ConfigurationIndexFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

theorem endpointStores_fields (d : Device) (pid : PeerId) (p : Peer) (e : Endpoint)
    (reset : Option UInt64) (resident : d.peers[pid]?=some p) :
    deviceFields (Config.endpointStores d pid p e reset)=deviceFields d := by
  unfold Config.endpointStores
  split
  · rfl
  · cases reset with
    | none => exact deviceFields_peerWrite d pid p _ resident rfl
    | some ts =>
      let written := {p with endpoint:=some e}
      let first := Config.withPeer d pid written
      have one := deviceFields_peerWrite d pid p written resident rfl
      have two := deviceFields_peerWrite first pid written
        {written with dstCache:={written.dstCache with resetTs:=ts}}
        (by simp [first,Config.withPeer]) rfl
      exact two.trans one

theorem endpoint_fields (pid : PeerId) (e : Endpoint) :
    SameView fields (setPeerEndpoint pid e) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have original := run
  unfold setPeerEndpoint at run
  simp only [requireNotPending,pure_bind] at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,suffix⟩ := run
  obtain ⟨state,ambient,d,device,resident⟩ := getPeer_normal pid w u p a c read
  subst u; subst c
  by_cases valid : e.family=AF_INET ∨ e.family=AF_INET6
  · obtain ⟨reset,effect,_,_⟩ := Config.setPeerEndpoint_exact pid e d p resident
      valid w.nlSock7 w.fixtureNetDevices w a result v b ⟨device,rfl,rfl⟩ original
    simp only [fields,device,effect,Option.map_some]
    exact congrArg some (endpointStores_fields d pid p e reset resident)
  · have no4 : (e.family==AF_INET)=false := by simp only [not_or] at valid; exact beq_eq_false_iff_ne.mpr valid.1
    have no6 : (e.family==AF_INET6)=false := by simp only [not_or] at valid; exact beq_eq_false_iff_ne.mpr valid.2
    obtain ⟨equal,out,after,compare,fact⟩ :=
      Config.endpointEq_returns_exact e p.endpoint (fun g=>g=w) w a rfl
    obtain ⟨_,state⟩ := fact
    subst out
    rw [MaterialOrigin.bind_ok_ambient] at suffix
    obtain ⟨eq,u,c,runCompare,rest⟩ := suffix
    rw [compare] at runCompare
    cases runCompare
    cases equal <;>
      simp [branch,no4,no6,AmbientM.branch] at rest <;>
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := rest <;> rfl

end Leanux.Proofs.WG.Index.ConfigurationIndex
