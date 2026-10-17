import Leanux.Proofs.WG.Config.FactoredTailSource
import Leanux.Proofs.WG.Config.BranchSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- A short-circuit put sequence either cancels or reaches its actual continuation
at exactly the residual room. Its branch trace is retained by the source helper. -/
theorem peerDumpPuts_returns (steps : List (Decision × Nat)) (skb : NlSkb)
    (cancel : PeerDumpResult) (next : NlSkb → WG.M PeerDumpResult)
    (expected : NlSkb → PeerDumpResult) (P : WGWorld → Prop)
    (tail : ∀ s, Returns (next s) P (fun result g => P g ∧ result = expected s)) :
    Returns (peerDumpPuts steps skb cancel next) P
      (fun result g => P g ∧ result =
        if (steps.map Prod.snd).sum ≤ skb.room then
          expected {skb with room := skb.room - (steps.map Prod.snd).sum}
        else cancel) := by
  induction steps generalizing skb with
  | nil => simpa [peerDumpPuts] using tail skb
  | cons step rest ih =>
    obtain ⟨site,cost⟩ := step
    by_cases short : skb.room < cost
    · have nofit : ¬ cost + (rest.map Prod.snd).sum ≤ skb.room := by omega
      simp only [peerDumpPuts,NlSkb.put,short,ite_true]
      refine returns_bind _ _ ((returns_iff _ _ _).mpr (branch_state_returns P site true)) ?_
      intro result g ambient pre
      obtain ⟨rfl,hp⟩ := pre
      exact ⟨cancel,g,ambient,rfl,hp,by simp [nofit]⟩
    · simp only [peerDumpPuts,NlSkb.put,short,ite_false]
      refine returns_bind _ _ ((returns_iff _ _ _).mpr (branch_state_returns P site false)) ?_
      intro result g ambient pre
      obtain ⟨rfl,hp⟩ := pre
      obtain ⟨value,final,after,run,preserved,effect⟩ := ih {skb with room := skb.room-cost} g ambient hp
      refine ⟨value,final,after,run,preserved,?_⟩
      rw [effect]
      by_cases fits : (rest.map Prod.snd).sum ≤ skb.room-cost
      · have enough : cost + (rest.map Prod.snd).sum ≤ skb.room := by omega
        simp [fits,enough,Nat.sub_sub]
      · have nofit : ¬ cost + (rest.map Prod.snd).sum ≤ skb.room := by omega
        simp [fits,nofit]

/-- The isolated endpoint tail is total for no stored allowed-IP entries. -/
theorem peerDumpEndpointTail_returns (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) (empty : p.allowedipsList = [])
    (P : WGWorld → Prop) :
    Returns (peerDumpEndpointTail p ctx skb0 skb pubkey attrs) P
      (fun result g => P g ∧ result = endpointDumpResult p ctx skb0 skb pubkey attrs) := by
  intro g ambient hp
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}
  by_cases v4 : (p.endpoint.map (·.family)).getD 0 = AF_INET
  · by_cases small : skb.room < 20
    · refine ⟨_,g,mark (mark ambient .getPeerEp4 true) .getPeerEpFail true,?_,hp,rfl⟩
      simp [peerDumpEndpointTail,getPeerDumpAllowedSource,empty,branch,AmbientM.branch,
        NlSkb.put,nlaTotal,v4,small,endpointDumpResult,mark,
        show ¬20 ≤ skb.room by omega]
      rfl
    · refine ⟨_,g,mark (mark (mark ambient .getPeerEp4 true) .getPeerEpFail false) .getPeerNoAips true,?_,hp,rfl⟩
      simp [peerDumpEndpointTail,getPeerDumpAllowedSource,empty,branch,AmbientM.branch,
        NlSkb.put,nlaTotal,v4,small,endpointDumpResult,mark,
        show 20 ≤ skb.room by omega]
      rfl
  · by_cases v6 : (p.endpoint.map (·.family)).getD 0 = AF_INET6
    · by_cases small : skb.room < 32
      · refine ⟨_,g,mark (mark (mark ambient .getPeerEp4 false) .getPeerEp6 true) .getPeerEpFail true,?_,hp,rfl⟩
        simp [peerDumpEndpointTail,getPeerDumpAllowedSource,empty,branch,AmbientM.branch,
          NlSkb.put,nlaTotal,v6,small,endpointDumpResult,mark,
          show AF_INET6 ≠ AF_INET by decide,
          beq_eq_false_iff_ne.mpr (show AF_INET6 ≠ AF_INET by decide),
          show ¬32 ≤ skb.room by omega]
        rfl
      · refine ⟨_,g,mark (mark (mark (mark ambient .getPeerEp4 false) .getPeerEp6 true) .getPeerEpFail false) .getPeerNoAips true,?_,hp,rfl⟩
        simp [peerDumpEndpointTail,getPeerDumpAllowedSource,empty,branch,AmbientM.branch,
          NlSkb.put,nlaTotal,v6,small,endpointDumpResult,mark,
          show AF_INET6 ≠ AF_INET by decide,
          beq_eq_false_iff_ne.mpr (show AF_INET6 ≠ AF_INET by decide),
          show 32 ≤ skb.room by omega]
        rfl
    · refine ⟨_,g,mark (mark (mark (mark ambient .getPeerEp4 false) .getPeerEp6 false) .getPeerEpFail false) .getPeerNoAips true,?_,hp,rfl⟩
      simp [peerDumpEndpointTail,getPeerDumpAllowedSource,empty,branch,AmbientM.branch,NlSkb.put,nlaTotal,v4,v6,
        endpointDumpResult,mark,beq_eq_false_iff_ne.mpr v4,beq_eq_false_iff_ne.mpr v6]
      rfl

/-- Exact total empty-IP serialization at every initial room, including cancellation. -/
theorem dumpTail_fixed_room (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (P : WGWorld → Prop) :
    Returns (getPeerDumpTailSource p ctx skb) P
      (fun result g => P g ∧ result = fixedPeerResult p ctx skb) := by
  let cancel : PeerDumpResult := (skb,ctx,.cancelled)
  let pubkey := hexKey p.remoteStatic
  let attrs := [("public_key",toJson pubkey)] ++
    [("preshared_key",toJson (hexKey p.presharedKey)),
     ("last_handshake",toJson (timespec p.walltimeLastHandshake)),
     ("keepalive",toJson p.persistentKeepaliveInterval),
     ("tx_bytes",toJson p.txBytes),("rx_bytes",toJson p.rxBytes),("protocol_version",toJson 1)]
  let expected (s : NlSkb) := if 96 ≤ s.room then
    endpointDumpResult p ctx skb {s with room := s.room-96} pubkey attrs else cancel
  have inner (s : NlSkb) :
      Returns (peerDumpPuts [(.getPeerPskFail,nlaTotal 32),(.getPeerPutHandshake,nlaTotal 16),
        (.getPeerPutKeepalive,nlaTotal 2),(.getPeerPutTx,nlaTotal 8),
        (.getPeerPutRx,nlaTotal 8),(.getPeerPutProto,nlaTotal 4)] s cancel
        (fun out => peerDumpEndpointTail p ctx skb out pubkey attrs)) P
        (fun result g => P g ∧ result = expected s) := by
    intro g ambient hp
    obtain ⟨result,final,after,run,preserved,effect⟩ := peerDumpPuts_returns
      [(.getPeerPskFail,nlaTotal 32),(.getPeerPutHandshake,nlaTotal 16),
       (.getPeerPutKeepalive,nlaTotal 2),(.getPeerPutTx,nlaTotal 8),
       (.getPeerPutRx,nlaTotal 8),(.getPeerPutProto,nlaTotal 4)] s cancel
      (fun out => peerDumpEndpointTail p ctx skb out pubkey attrs)
      (fun out => endpointDumpResult p ctx skb out pubkey attrs) P
      (fun out => peerDumpEndpointTail_returns p ctx skb out pubkey attrs empty P) g ambient hp
    refine ⟨result,final,after,run,preserved,?_⟩
    change result = (if 96 ≤ s.room then
      endpointDumpResult p ctx skb {s with room := s.room-96} pubkey attrs else cancel) at effect
    exact effect
  have broad : Returns (peerDumpFactoredTail p ctx skb) P
      (fun result g => P g ∧ result =
        if 40 ≤ skb.room then expected {skb with room := skb.room-40} else cancel) := by
    unfold peerDumpFactoredTail
    apply (show Returns _ P _ from ?_)
    have afterPublic (s : NlSkb) : Returns
        (do
          if ← branch .getPeerFirst ctx.nextAllowedip.isNone then
            peerDumpPuts [(.getPeerPskFail,nlaTotal 32),(.getPeerPutHandshake,nlaTotal 16),
              (.getPeerPutKeepalive,nlaTotal 2),(.getPeerPutTx,nlaTotal 8),
              (.getPeerPutRx,nlaTotal 8),(.getPeerPutProto,nlaTotal 4)] s cancel
              (fun out => peerDumpEndpointTail p ctx skb out pubkey attrs)
          else getPeerDumpAllowedSource p ctx skb s pubkey [("public_key",toJson pubkey)] ctx.nextAllowedip)
        P (fun result g => P g ∧ result = expected s) := by
      simp only [fresh,Option.isNone_none]
      refine returns_bind _ _ ((returns_iff _ _ _).mpr (branch_state_returns P .getPeerFirst true)) ?_
      intro value g ambient pre
      obtain ⟨rfl,hp⟩ := pre
      exact inner s g ambient hp
    simpa [nlaTotal,List.map,List.sum,cancel,pubkey,attrs] using peerDumpPuts_returns
      [(.getPeerNoNest,nlaTotal 0),(.getPeerPubkeyFail,nlaTotal 32)] skb cancel _ expected P afterPublic
  intro g ambient hp
  obtain ⟨result,final,after,run,preserved,effect⟩ := broad g ambient hp
  refine ⟨result,final,after,?_,preserved,?_⟩
  · rw [peerDumpTail_factored]; exact run
  · rw [effect]
    let cost := if (p.endpoint.map (·.family)).getD 0 = AF_INET then 20
      else if (p.endpoint.map (·.family)).getD 0 = AF_INET6 then 32 else 0
    have space : peerFixedSpace p = 136+cost := rfl
    by_cases h40 : 40 ≤ skb.room
    · by_cases h96 : 96 ≤ skb.room-40
      · by_cases endpoint : cost ≤ skb.room-136
        · have enough : peerFixedSpace p ≤ skb.room := by omega
          have enoughCost : 136+cost ≤ skb.room := by omega
          dsimp only [cost] at endpoint enoughCost
          simp [h40,expected,h96,endpointDumpResult,cost,endpoint,fixedPeerResult,enoughCost,
            attrs,pubkey,peerFixedAttrs,space,Nat.sub_sub,← Nat.add_assoc]
          cases p.endpoint <;> rfl
        · have notEnough : ¬peerFixedSpace p ≤ skb.room := by omega
          dsimp only [cost] at endpoint
          simp [h40,expected,h96,endpointDumpResult,endpoint,fixedPeerResult,notEnough,cancel,Nat.sub_sub]
      · have notEnough : ¬peerFixedSpace p ≤ skb.room := by omega
        simp [h40,expected,h96,fixedPeerResult,notEnough,cancel]
    · have notEnough : ¬peerFixedSpace p ≤ skb.room := by omega
      simp [h40,fixedPeerResult,notEnough,cancel]


end Leanux.Proofs.WG.Config
