import Leanux.Proofs.WG.Config.MixedPeerSerializerModel
import Leanux.Proofs.WG.Config.FactoredTailReturns
import Leanux.Proofs.WG.Config.MixedDumpScanSource
import Leanux.Proofs.WG.Config.MultipartLeaves

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

theorem dumpAllowed_weighted_room (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb) (pubkey : String)
    (attrs : List (String × Json)) (ids : List NodeId)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (selected : ∀ start, ids.head? = some start → p.allowedipsList.dropWhile (· != start) = ids)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    Returns (getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs ids.head?)
      (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = weightedAllowedResult d nodes ctx skb0 skb pubkey attrs ids) := by
  cases ids with
  | nil =>
    intro g ambient device
    refine ⟨_,g,{ambient with steps := ambient.steps.push {
      decision := .getPeerNoAips,outcome := true,netRx := ambient.netRxSection}},?_,device,rfl⟩
    simp [getPeerDumpAllowedSource,weightedAllowedResult,branch,AmbientM.branch]
    rfl
  | cons start ids =>
    have suffix := selected start rfl
    by_cases shortNest : skb.room < 4
    · intro g ambient device
      let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
        {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}
      let a0 := mark ambient .getPeerNoAips false
      let a1 := mark a0 .getPeerSeqUnset (ctx.allowedipsSeq == 0)
      let a2 := if ctx.allowedipsSeq = 0 then a1 else mark a1 .getPeerSeqChanged false
      let after := mark a2 .getPeerAipsNestFail true
      refine ⟨_,g,after,?_,device,rfl⟩
      by_cases zero : ctx.allowedipsSeq = 0
      · simp [getPeerDumpAllowedSource,weightedAllowedResult,shortNest,branch,AmbientM.branch,
          getDev,device,zero,NlSkb.put,nlaTotal,after,a2,a1,a0,mark]
        rfl
      · have stable : ctx.allowedipsSeq = d.peerAllowedips.seq := sequence.resolve_left zero
        have nonzero : d.peerAllowedips.seq ≠ 0 := by intro eq; exact zero (stable.trans eq)
        have sameCtx : {ctx with allowedipsSeq := d.peerAllowedips.seq} = ctx := by cases ctx; simp_all
        simp [getPeerDumpAllowedSource,weightedAllowedResult,shortNest,branch,AmbientM.branch,
          getDev,device,stable,nonzero,NlSkb.put,nlaTotal,after,a2,a1,a0,mark,sameCtx]
        rfl
    · have facts := weightedPrefix_spec nodes (skb.room-4) (start::ids)
      cases plan : weightedPrefix nodes (skb.room-4) (start::ids) with
      | mk front remaining =>
        rw [plan] at facts
        dsimp only at facts
        cases remaining with
        | nil =>
          have decomp : front = start::ids := by simpa using facts.1
          have reads : ∀ id ∈ front, d.nodes[id]? = some (nodes id) := by simpa only [decomp] using readable
          have actual := dumpAllowed_weighted_all d nodes p ctx skb0 skb pubkey attrs start front
            reads (by rw [decomp]; exact suffix) (by rw [decomp]; simp) sequence (by omega)
          simpa only [List.head?_cons,weightedAllowedResult,shortNest,ite_false,plan] using actual
        | cons next tail =>
          have decomp : front ++ next::tail = start::ids := facts.1
          have reads : ∀ id ∈ front ++ [next], d.nodes[id]? = some (nodes id) := by
            intro id member
            apply readable id
            rw [← decomp]
            simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
            rcases member with member | same
            · exact .inl member
            · exact .inr (.inl same)
          have short := facts.2.2 next tail rfl
          have actual := dumpAllowed_weighted_split d nodes p ctx skb0 skb pubkey attrs start front next tail
            reads (by rw [decomp]; exact suffix) sequence (by omega) (by omega)
          simpa only [List.head?_cons,weightedAllowedResult,shortNest,ite_false,plan] using actual

theorem peerDumpEndpointTail_weighted_returns (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb) (ids : List NodeId)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    Returns (peerDumpEndpointTail p ctx skb0 skb (hexKey p.remoteStatic)
      (peerFixedAttrs {p with endpoint := none}))
      (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = weightedEndpointResult d nodes p ctx skb0 skb ids) := by
  intro g ambient device
  let family := (p.endpoint.map (·.family)).getD 0
  let cost := if family = AF_INET then 20 else if family = AF_INET6 then 32 else 0
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}
  let ep4 := mark ambient .getPeerEp4 (family == AF_INET)
  let before := mark (if family = AF_INET then ep4 else mark ep4 .getPeerEp6 (family == AF_INET6))
    .getPeerEpFail (skb.room < cost)
  have source : ((peerDumpEndpointTail p ctx skb0 skb (hexKey p.remoteStatic)
        (peerFixedAttrs {p with endpoint := none})).run g).run ambient =
      if cost ≤ skb.room then
        ((getPeerDumpAllowedSource p ctx skb0 {skb with room := skb.room-cost}
          (hexKey p.remoteStatic) (peerFixedAttrs p) ids.head?).run g).run before
      else .ok (((skb0,ctx,.cancelled),g),before) := by
    simp only [← Nat.not_lt]
    by_cases v4 : family = AF_INET <;> by_cases v6 : family = AF_INET6 <;>
      by_cases short : skb.room < cost
    all_goals simp_all [peerDumpEndpointTail,peerFixedAttrs,branch,AmbientM.branch,NlSkb.put,
      nlaTotal,family,cost,before,ep4,mark]
    all_goals try simp_all only [← Nat.not_lt,ite_false,Bool.false_eq_true,decide_false]
    all_goals cases p.endpoint <;> rfl
  by_cases fits : cost ≤ skb.room
  · have selected : ∀ start, ids.head? = some start → p.allowedipsList.dropWhile (· != start) = ids := by
      cases ids with
      | nil => simp
      | cons first rest => intro start head; cases head; simp [listed]
    obtain ⟨result,final,after,run,finalDevice,value⟩ :=
      dumpAllowed_weighted_room d nodes p ctx skb0 {skb with room := skb.room-cost}
        (hexKey p.remoteStatic) (peerFixedAttrs p) ids readable selected sequence g before device
    refine ⟨result,final,after,?_,finalDevice,?_⟩
    · rw [source,ite_eq_left fits]; exact run
    · change result = (if cost ≤ skb.room then _ else _)
      rw [ite_eq_left fits]
      exact value
  · refine ⟨(skb0,ctx,.cancelled),g,before,?_,device,?_⟩
    · rw [source,ite_eq_right fits]
    · change (skb0,ctx,PeerDump.cancelled) = (if cost ≤ skb.room then _ else _)
      rw [ite_eq_right fits]

theorem dumpTail_weighted_resume_room (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (start : NodeId) (ids : List NodeId)
    (cursor : ctx.nextAllowedip = some start)
    (head : ids.head? = some start)
    (selected : p.allowedipsList.dropWhile (· != start) = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    Returns (getPeerDumpTailSource p ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = weightedPeerResult d nodes p ctx skb ids) := by
  let P : WGWorld → Prop := fun g => g.dev = some d
  let expected (s : NlSkb) := weightedAllowedResult d nodes ctx skb s (hexKey p.remoteStatic)
    [("public_key",toJson (hexKey p.remoteStatic))] ids
  have afterPublic (s : NlSkb) : Returns
      (do
        if ← branch .getPeerFirst ctx.nextAllowedip.isNone then
          peerDumpPuts [(.getPeerPskFail,nlaTotal 32),(.getPeerPutHandshake,nlaTotal 16),
            (.getPeerPutKeepalive,nlaTotal 2),(.getPeerPutTx,nlaTotal 8),
            (.getPeerPutRx,nlaTotal 8),(.getPeerPutProto,nlaTotal 4)] s (skb,ctx,.cancelled)
            (fun out => peerDumpEndpointTail p ctx skb out (hexKey p.remoteStatic)
              (peerFixedAttrs {p with endpoint := none}))
        else getPeerDumpAllowedSource p ctx skb s (hexKey p.remoteStatic) [("public_key",toJson (hexKey p.remoteStatic))] ctx.nextAllowedip)
      P (fun result g => P g ∧ result = expected s) := by
    simp only [cursor,Option.isNone_some]
    refine returns_bind _ _ ((returns_iff _ _ _).mpr (branch_state_returns P .getPeerFirst false)) ?_
    intro value g ambient pre
    obtain ⟨rfl,hp⟩ := pre
    have pick : ∀ next, ids.head? = some next → p.allowedipsList.dropWhile (· != next) = ids := by
      intro next eq
      rw [head] at eq
      cases eq
      exact selected
    simpa only [head,Bool.false_eq_true,ite_false] using dumpAllowed_weighted_room d nodes p ctx skb s (hexKey p.remoteStatic)
      [("public_key",toJson (hexKey p.remoteStatic))] ids readable pick sequence g ambient hp
  have actual := peerDumpPuts_returns
    [(.getPeerNoNest,nlaTotal 0),(.getPeerPubkeyFail,nlaTotal 32)] skb (skb,ctx,.cancelled)
    _ expected P afterPublic
  rw [peerDumpTail_factored]
  simpa [peerDumpFactoredTail,weightedPeerResult,cursor,expected,P,peerFixedAttrs,
    nlaTotal,List.map,List.sum] using actual

theorem dumpTail_weighted_fresh_room (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId)
    (fresh : ctx.nextAllowedip = none) (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    Returns (getPeerDumpTailSource p ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = weightedPeerResult d nodes p ctx skb ids) := by
  let P : WGWorld → Prop := fun g => g.dev = some d
  let cancel : PeerDumpResult := (skb,ctx,.cancelled)
  let pubkey := hexKey p.remoteStatic
  let attrs := [("public_key",toJson pubkey)] ++
    [("preshared_key",toJson (hexKey p.presharedKey)),
     ("last_handshake",toJson (timespec p.walltimeLastHandshake)),
     ("keepalive",toJson p.persistentKeepaliveInterval),
     ("tx_bytes",toJson p.txBytes),("rx_bytes",toJson p.rxBytes),("protocol_version",toJson 1)]
  let expected (s : NlSkb) := if 96 ≤ s.room then
    weightedEndpointResult d nodes p ctx skb {s with room := s.room-96} ids else cancel
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
      (fun out => weightedEndpointResult d nodes p ctx skb out ids) P
      (fun out => peerDumpEndpointTail_weighted_returns d nodes p ctx skb out ids listed readable sequence) g ambient hp
    refine ⟨result,final,after,run,preserved,?_⟩
    change result = (if 96 ≤ s.room then
      weightedEndpointResult d nodes p ctx skb {s with room := s.room-96} ids else cancel) at effect
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
          simp [h40,expected,h96,weightedEndpointResult,cost,endpoint,weightedPeerResult,fresh,enoughCost,
            space,Nat.sub_sub,← Nat.add_assoc]
        · have notEnough : ¬peerFixedSpace p ≤ skb.room := by omega
          dsimp only [cost] at endpoint
          simp [h40,expected,h96,weightedEndpointResult,endpoint,weightedPeerResult,fresh,notEnough,cancel,Nat.sub_sub]
      · have notEnough : ¬peerFixedSpace p ≤ skb.room := by omega
        simp [h40,expected,h96,weightedPeerResult,fresh,notEnough,cancel]
    · have notEnough : ¬peerFixedSpace p ≤ skb.room := by omega
      simp [h40,weightedPeerResult,fresh,notEnough,cancel]

/-- Actual fresh peer serializer at every room, including fixed-prefix and AIP-nest
cancellation and a zero-node first split. No callback-success premise is supplied. -/
theorem getPeerDump_weighted_fresh_room (pid : PeerId) (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId)
    (resident : d.peers[pid]? = some p)
    (fresh : ctx.nextAllowedip = none) (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    Returns (getPeerDump pid ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = weightedPeerResult d nodes p ctx skb ids) :=
  multipart_getter_returns pid d p ctx skb _ resident
    (dumpTail_weighted_fresh_room d nodes p ctx skb ids fresh listed readable sequence)

/-- Actual continuation selected by the stored allowed-IP cursor, with arbitrary
room and all weighted node widths; the source's first nonfit is retained. -/
theorem getPeerDump_weighted_resume_room (pid : PeerId) (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (start : NodeId) (ids : List NodeId)
    (resident : d.peers[pid]? = some p)
    (cursor : ctx.nextAllowedip = some start) (head : ids.head? = some start)
    (selected : p.allowedipsList.dropWhile (· != start) = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    Returns (getPeerDump pid ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = weightedPeerResult d nodes p ctx skb ids) :=
  multipart_getter_returns pid d p ctx skb _ resident
    (dumpTail_weighted_resume_room d nodes p ctx skb start ids cursor head selected readable sequence)

end Leanux.Proofs.WG.Config
