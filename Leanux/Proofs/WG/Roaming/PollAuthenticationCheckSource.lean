import Leanux.Proofs.WG.Roaming.PollAuthenticationCheckBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes PublicationIdentity
open Origins.HistorySupport (sessions)


theorem check_authenticated (trace : Runner.Trace) (placeholders : Bool)
    (q : Check) (occurs : q.Occurs trace placeholders) :
    ∃ e : Authentication, e.Valid trace placeholders q ∧ e.Facts q := by
  obtain ⟨pre,post,n,id,stamp,pkt,r,position,matched⟩ := occurs
  have certificate := Initialized.checkedEndpoint trace placeholders pre post n id stamp pkt r position
  obtain ⟨valid,value,family,before,after,decrypt,out,published,ambient,
    earlier,publication,retained,packet,stampEq⟩ := certificate
  obtain ⟨d,k,p,afterDev,hd,hpkt,hkey,keyValid,owner,support,shape,aead,
    publishStamp,hpeer,hpublished,publishEpoch,publishPacket,publishPeer⟩ := retained.1
  obtain ⟨material,ctx,originalDev,original,member,mvalid,mvalue,slot,configured,
    originalDevice,originalEpoch,originalStored,originalValid,originalWord,
    sameMaterial,word,identity⟩ := support
  let e := authenticationProjects before.length decrypt k material ctx original
  have keyAt : (decrypt.before.dev.bind fun d => d.keypairs[decrypt.value.1.keypair]?) =
      some k := by simp only [hd,Option.bind_some,hkey]
  have originalAt : originalDev.keypairs[ctx.slot]? = some original := by
    simpa only [slot] using originalStored
  refine ⟨e,?_,?_⟩
  · exact ⟨pre,post,before,after,n,id,stamp,pkt,r,decrypt,out,published,ambient,k,
      material,ctx,originalDev,original,position,matched,valid,earlier,publication,
      retained,packet,stampEq,keyAt,member,mvalid,mvalue,configured,originalDevice,
      originalAt,sameMaterial,rfl⟩
  · subst q
    obtain ⟨sessionDev,sessionDevice,sessionPeer,registered,alive,configuredWord⟩ := configured
    have order : before.length < pre.length := by
      rw [earlier,List.length_append,List.length_cons]
      omega
    have packetAt : (r.before.wg.dev.bind fun d => d.rxSkbs[id]?) = some pkt := by
      simpa only [RxDisposition.nativeRxStore,packet] using retained.2.2.1
    refine ⟨⟨value,family,packetAt⟩,order,?_,keyAt,keyValid,owner,?_,?_,slot,
      ⟨sessionDev,sessionDevice,sessionPeer,registered⟩,alive,word,?_,
      originalValid,originalWord,sameMaterial,?_⟩
    · change (decrypt.before.dev.bind fun d => d.rxSkbs[id]?) = some decrypt.value.1
      simp only [hd,Option.bind_some,hpkt]
    · change pkt = {decrypt.value.1 with nonce := u64le decrypt.value.1.bytes 8, bytes := pkt.bytes,state := .crypted}
      rw [packet,shape]
    · change aeadDecrypt k.receiving.key (counterNonce (u64le decrypt.value.1.bytes 8))
        (decrypt.value.1.bytes.drop 16) [] = some pkt.bytes
      simpa only [packet] using aead
    · change (material.after.dev.bind fun d => d.keypairs[ctx.slot]?) = some original
      simp only [originalDevice,Option.bind_some,originalAt]
    · intro current currentAt
      change (r.before.wg.dev.bind fun d => d.peers[pkt.peer]?) = some current at currentAt
      obtain ⟨currentDev,currentDevice,currentStored⟩ := Option.bind_eq_some_iff.mp currentAt
      have survives := retained.2.2.2 currentDev current currentDevice currentStored
      have oldIdentity := identity p hpeer
      have storedIdentity : CurrentIdentity.identity p = CurrentIdentity.identity current := by
        simpa only [CurrentIdentity.peerView,hpublished,Option.map_some,
          Option.bind_some,publishPeer,Option.some.injEq,CurrentIdentity.identity] using survives
      exact storedIdentity.symm.trans oldIdentity

theorem getElem_split {α : Type} {xs : List α} {i : Nat} {x : α}
    (atIndex : xs[i]? = some x) :
    ∃ pre post, xs = pre ++ x :: post ∧ pre.length = i := by
  obtain ⟨bound,entry⟩ := List.getElem?_eq_some_iff.mp atIndex
  refine ⟨xs.take i,xs.drop (i+1),?_,?_⟩
  · have split := List.take_append_drop i xs
    rw [List.drop_eq_getElem_cons bound,entry] at split
    exact split.symm
  · simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt bound)]

theorem check_mem_iff (trace : Runner.Trace) (placeholders : Bool) (q : Check) :
    q ∈ checks trace placeholders ↔ q.Occurs trace placeholders := by
  constructor
  · intro member
    obtain ⟨⟨event,index⟩,member,found⟩ := List.mem_filterMap.mp member
    have atIndex := List.mk_mem_zipIdx_iff_getElem?.mp member
    cases event <;> simp only [extractCheck,reduceCtorEq] at found
    rename_i n id stamp pkt receipt
    obtain ⟨pre,post,split,length⟩ := getElem_split atIndex
    refine ⟨pre,post,n,id,stamp,pkt,receipt,split,?_⟩
    simpa only [Option.some.injEq,length] using found.symm
  · rintro ⟨pre,post,n,id,stamp,pkt,r,split,matched⟩
    apply List.mem_filterMap.mpr
    refine ⟨(.checkedEndpoint n id stamp pkt r,pre.length),?_,?_⟩
    · apply List.mk_mem_zipIdx_iff_getElem?.mpr
      simp only [split,List.getElem?_append_right (l₁ := pre) (Nat.le_refl pre.length),Nat.sub_self,
        List.getElem?_cons_zero]
    · simpa only [extractCheck] using congrArg some matched.symm



end Leanux.Proofs.WG.Roaming.PollAuthentication
