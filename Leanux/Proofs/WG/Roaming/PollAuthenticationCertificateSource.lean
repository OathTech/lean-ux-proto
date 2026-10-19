import Leanux.Proofs.WG.Roaming.PollAuthenticationCertificateBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes PublicationIdentity
open Origins.HistorySupport (sessions)

theorem endpoint_value {pkt : RxPacket} {r : RunWitness (Option Endpoint)}
    (valid : r.Valid (liftWG (endpointFromSkb pkt.source))) :
    r.value = some (sourceEndpoint pkt.source) ∧
      (pkt.source.family = 4 ∨ pkt.source.family = 6) := by
  change (liftWG (endpointFromSkb pkt.source)).run r.before = .ok (r.value,r.after) at valid
  rw [liftWG_run] at valid
  cases native : ((endpointFromSkb pkt.source).run r.before.wg).run r.before.ambient with
  | error stop => simp only [native,Except.map] at valid; cases valid
  | ok out =>
    obtain ⟨⟨value,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
    obtain ⟨rfl,same⟩ := valid
    exact ((Noise.ensures_iff _ _ _).mpr (endpointFromSkb_exact pkt.source (fun _=>True))
      _ _ _ _ _ True.intro native).2

theorem certificate {history : List RxHistory.Event} {n id : Nat}
    {stamp : PacketStamp} {pkt : RxPacket} {r : RunWitness (Option Endpoint)}
    (facts : EventFacts history (.checkedEndpoint n id stamp pkt r))
    (valid : RxDisposition.EventValid (.checkedEndpoint n id stamp pkt r)) :
    Certified history id stamp pkt r := by
  exact ⟨valid,(endpoint_value valid).1,(endpoint_value valid).2,
    selected_anchored facts.1 facts.2.1 facts.2.2⟩

theorem Certified.append {history : List RxHistory.Event} {id : SkbId}
    {stamp : PacketStamp} {pkt : RxPacket} {r : RunWitness (Option Endpoint)}
    (certified : Certified history id stamp pkt r) (suffix : List RxHistory.Event) :
    Certified (history++suffix) id stamp pkt r := by
  obtain ⟨valid,value,family,prior,later,decrypt,out,published,ambient,
    position,publication,retained,packet,stampEq⟩ := certified
  exact ⟨valid,value,family,prior,later++suffix,decrypt,out,published,ambient,
    by simp only [position,List.append_assoc,List.cons_append],
    publication,retained,packet,stampEq⟩

/-- Residency at the attempted setter input supplies the current identity.
It may come from that setter's first successful getter; its later tail need
not return. The certificate itself retains only conditional peer survival. -/
theorem Certified.live_of_resident {history : List RxHistory.Event} {id : SkbId}
    {stamp : PacketStamp} {pkt : RxPacket} {r : RunWitness (Option Endpoint)}
    (certified : Certified history id stamp pkt r)
    (resident : ∃ d p, r.before.wg.dev=some d ∧ d.peers[pkt.peer]?=some p) :
    ∃ prior later, ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)),
      ∃ out published ambient,
      history = prior ++ .rx (.decrypt id decrypt) :: later ∧
      Published id decrypt out pkt.peer published ambient ∧
      Live (sessions prior) id decrypt out pkt.peer published r.before.wg ∧
      pkt = {out with state := .crypted} ∧ stamp = packetStamp published id := by
  obtain ⟨_,_,_,prior,later,decrypt,out,published,ambient,
    position,publication,retained,packet,stampEq⟩ := certified
  exact ⟨prior,later,decrypt,out,published,ambient,position,publication,
    retained.live resident,packet,stampEq⟩

theorem poll_certificates (history : List RxHistory.Event) (pid : PeerId)
    (budget : Nat) (w : World) (prior : List LifetimeEvent)
    (hi : PublicationHistory.Inv history w.wg) :
    ∀ n id stamp pkt r,
      RxJoint.Event.checkedEndpoint n id stamp pkt r ∈
        (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed prior)).2 →
      Certified history id stamp pkt r := by
  intro n id stamp pkt r member
  exact certificate (poll_seed history pid budget w prior hi _ member)
    (RxDisposition.poll_seed_valid pid budget w prior _ member)

theorem observePoll_certificates (history : List RxHistory.Event) (pid : PeerId)
    (budget : Nat) (w : World) (hi : PublicationHistory.Inv history w.wg) :
    ∃ suffix : List RxJoint.Event, runPrefix (RxHistory.observePoll pid budget) w history =
      ((runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior history))).1,
        history ++ suffix.map RxHistory.promote) ∧
      ∀ n id stamp pkt r,
        RxJoint.Event.checkedEndpoint n id stamp pkt r ∈ suffix →
        Certified history id stamp pkt r := by
  obtain ⟨suffix,append⟩ := RxJoint.poll_appends pid budget w
    (RxJoint.seed (RxHistory.prior history))
  refine ⟨suffix,RxHistory.observePoll_suffix pid budget w history _ suffix (Prod.ext rfl append),?_⟩
  intro n id stamp pkt r member
  apply poll_certificates history pid budget w (RxHistory.prior history) hi n id stamp pkt r
  rw [append]
  exact List.mem_append_right _ member

theorem safe_append {h t : List RxHistory.Event} (prior : Safe h)
    (added : ∀pre n id stamp pkt r post,
      t=pre ++ .checkedEndpoint n id stamp pkt r :: post →
      Certified (h++pre) id stamp pkt r) : Safe (h++t) := by
  let checked : List RxHistory.Event → RxHistory.Event → Prop := fun pre e=>
    match e with
    | .checkedEndpoint _ id stamp pkt r=>Certified pre id stamp pkt r
    | _=>True
  have before : ∀pre e post,h=pre++e::post→checked pre e := by
    intro pre e post position
    cases e <;> first | trivial | exact prior _ _ _ _ _ _ _ position
  have after : ∀pre e post,t=pre++e::post→checked (h++pre) e := by
    intro pre e post position
    cases e <;> first | trivial | exact added _ _ _ _ _ _ _ position
  have result := (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    checked h t before after
  intro pre n id stamp pkt r post position
  exact result pre (.checkedEndpoint n id stamp pkt r) post position

/-- The existing original RX observer is unchanged. Endpoint certificates
survive a later Stop; normal state is the landed publication/owner invariant. -/
theorem observePoll (pid : PeerId) (budget : Nat) :
    PrefixPreserves Reached (fun h=>PublicationJoint.Safe h ∧ Safe h)
      (RxHistory.observePoll pid budget) := by
  intro w h hi
  obtain ⟨suffix,run,certificates⟩ := observePoll_certificates h pid budget w hi.1.2.1.1
  have endpointSafe : Safe (h ++ suffix.map RxHistory.promote) := by
    apply safe_append hi.2
    intro pre n id stamp pkt r post position
    have member : RxHistory.Event.checkedEndpoint n id stamp pkt r ∈
        suffix.map RxHistory.promote := by rw [position]; simp
    obtain ⟨e,present,equal⟩ := List.mem_map.mp member
    cases e <;> simp only [RxHistory.promote] at equal <;> cases equal
    exact (certificates n id stamp pkt r present).append pre
  obtain ⟨_,_,publicationSafe,normal⟩ := PublicationJoint.poll pid budget w h hi.1
  refine ⟨suffix.map RxHistory.promote,congrArg Prod.snd run,?_,?_⟩
  · exact ⟨publicationSafe,by simpa only [run] using endpointSafe⟩
  · cases result : (runPrefix (RxHistory.observePoll pid budget) w h).1 with
    | error stop=>trivial
    | ok out=>
      exact ⟨by simpa only [result] using normal,by simpa only [run] using endpointSafe⟩

end Leanux.Proofs.WG.Roaming.PollAuthentication
