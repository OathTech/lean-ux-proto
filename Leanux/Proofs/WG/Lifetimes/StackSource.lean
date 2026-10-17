import Leanux.Proofs.WG.Lifetimes.StackAccess
import Leanux.Proofs.Logged.ProjectsPrefix
import Leanux.Proofs.Logged.ProjectsUnder
import Leanux.Proofs.Logged.PrefixBatch

/-! Shared source cuts for the actual Stack observers. Only the named callback
is parameterized; all other actions remain their original product lifts. Exact
specializations retain every input and both normal and stopped outcomes. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing

def reply4With {E : Type}
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int) (dst : Nat) (bytes : List UInt8) : PrefixM E Unit := do
  liftPrefix (skipCut ([.inetEhashSecret] ++ allocCuts))
  let saddr := WG.beAt bytes 12 4
  match ← liftPrefix (liftWG (liftRouting (Net.routeOutput4 saddr dst))) with
  | .error _ => return
  | .ok r =>
    if r.dev != WG0_IFINDEX then
      liftPrefix (unsupported "a stack reply routed away from wg0")
    let devMtu := (← liftPrefix (liftWG getDev)).mtu
    let mtu := if r.mtu != 0 then r.mtu else devMtu
    liftPrefix (liftWG (liftRouting (Net.neighbourClassify WG0_IFINDEX)))
    discard <| xmit 4 dst [{bytes, csum := none, mtu}] mtu

def receive4With {E : Type}
    (reply : Nat → List UInt8 → PrefixM E Unit) (pkt : List UInt8) : PrefixM E Unit := do
  let byte (i : Nat) : Nat := (pkt.getD i 0).toNat
  let ihl := byte 0 % 16
  -- row 1 (ip_rcv_core, ip_input.c:496): ihl < 5; row 2: tot_len < ihl*4
  -- at the pull (:506); row 14: options (ip_rcv_options)
  if ihl < 5 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 1 (ihl < 5: ip_rcv_core drops it)")
  if ihl > 5 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 14 (IPv4 options)")
  let totLen := WG.beAt pkt 2 2
  if totLen != pkt.length then liftPrefix (invariant "consume_data_done trims to tot_len")
  -- row 3: ip_fast_csum over the header
  if onesSum (pkt.take 20) != 0xffff then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 3 (a bad IPv4 header checksum)")
  let src := WG.beAt pkt 12 4
  let dst := WG.beAt pkt 16 4
  let top := src / 2 ^ 24
  -- rows 5-11: the route (ip_route_input_slow): martian sources, zeronet
  -- and loopback destinations, the limited broadcast, multicast groups
  if src ≥ 0xe0000000 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 5 (a multicast or limited-broadcast source)")
  if dst == 0xffffffff then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 10 (the limited broadcast destination)")
  if top == 0 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 6 (a zeronet source)")
  if dst / 2 ^ 24 == 0 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 7 (a zeronet destination)")
  if dst / 2 ^ 24 == 127 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 8 (a loopback destination, route_localnet 0)")
  if top == 127 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 9 (a loopback source)")
  if dst / 2 ^ 28 == 0xe then liftPrefix (Leanux.Env.Stack.excluded "2.2 rows 11a-11c (a multicast destination)")
  -- The route verdict is obtained by the actual trie lookup and source test.
  match ← liftPrefix (liftWG (liftRouting (Net.routeInput4 src dst))) with
  | .local true =>
    liftPrefix (Stack.excluded "2.2 row 12 (a local source: fib_validate_source's -EINVAL)")
  | .local false => pure ()
  | .noRoute | .notLocal => return
  | .broadcast =>
    liftPrefix (unsupported "a decrypted packet to a broadcast route (udp.c's broadcast delivery)")
  -- row 15: fragments
  if WG.beAt pkt 6 2 % 0x4000 != 0 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 15 (a fragment)")
  let protocol := byte 9
  if protocol == 6 then
    -- row 17: tcp_v4_rcv (tcp_ipv4.c:2209-2231): a pullable header with
    -- doff >= 5, else silent; TCP options are a shape the mirror refuses
    if totLen < 40 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 17 (a TCP segment shorter than its header)")
    let doff := byte 32 / 16
    if doff < 5 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 17 (doff < 5)")
    if doff > 5 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 17 (TCP options)")
    -- no socket: tcp_v4_send_reset; a segment with RST is never answered
    if byte 33 / 4 % 2 == 1 then liftPrefix (Leanux.Env.Stack.excluded "2.4.1 (a segment with RST is not answered)")
    reply src (Stack.rst4 pkt)
    return
  if protocol != 17 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 16 (a protocol without a handler: ICMP protocol unreachable)")
  -- rows 18-21: the UDP length against the IP payload
  let ulen := WG.beAt pkt 24 2
  if ulen > totLen - 20 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 18 (ulen beyond the IPv4 payload)")
  if ulen < 8 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 19 (ulen < 8)")
  if ulen < totLen - 20 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 20 (a datagram trimmed to ulen)")
  -- rows 22-24: the port map of the fixture
  let dport := WG.beAt pkt 22 2
  if dport != SENDER_PORT then
    if (← liftPrefix getWG).dev.any (fun d => d.running && dport == d.incomingPort) then
      liftPrefix (Leanux.Env.Stack.excluded "2.2 row 24 (wg0's own listen port: a nested receive)")
    liftPrefix (Leanux.Env.Stack.excluded "2.2 row 22 (no socket at the port: ICMP port unreachable)")
  -- row 23: delivered to the sender, with the inner TOS (after the ECN
  -- rewrite) and the destination its `IPV6_PKTINFO` reports (v4-mapped)
  liftPrefix (modifyEnv fun w => { w with senderInbox := w.senderInbox ++
    [{ family := AF_INET, addr := src, port := WG.beAt pkt 20 2, bytes := pkt.drop 28, tos := byte 1,
       dst := 0xffff00000000 + dst }] })

def stackReceiveWith {E : Type}
    (receive4 : List UInt8 → PrefixM E Unit) (pkt : List UInt8) : PrefixM E Unit := do
  let version := (pkt.headD 0).toNat / 16
  if version == 4 then receive4 pkt
  else if version == 6 then liftPrefix (Stack.receive6 pkt)
  else liftPrefix (invariant "consume_data_done passed a packet that is neither IPv4 nor IPv6")

/-- The existing observer is the actual source with its original native TX observer. -/
theorem reply4Prefix_factor (dst : Nat) (bytes : List UInt8) :
    reply4Prefix dst bytes =
      reply4With (fun family addr pkts mtu => liftWGObserver (wgXmitPrefix family addr pkts mtu)) dst bytes := rfl

theorem receive4Prefix_factor (pkt : List UInt8) :
    receive4Prefix pkt = receive4With reply4Prefix pkt := rfl

theorem stackReceivePrefix_factor (pkt : List UInt8) :
    stackReceivePrefix pkt = stackReceiveWith receive4Prefix pkt := rfl

/-- A stopped product leaf retains exactly its old journal; its continuation
is unreachable, independently of either callback's event type. -/
private theorem stack_projects_failure {E F α β : Type} (ρ : E → Option F)
    (a : Leanux.M α) (fails : ∀ w, ∃ stop, a.run w = .error stop)
    (g : α → PrefixM E β) (f : α → PrefixM F β) :
    ProjectsPrefix ρ id (liftPrefix a >>= g) (liftPrefix a >>= f) := by
  intro w h
  obtain ⟨stop,hr⟩ := fails w
  simp only [runPrefix_bind,runPrefix_lift,hr]
  rfl

/-- Projection preserves the original product state, exact Stop, and projected
journal for every incoming history. Only the arbitrary TX callbacks are related. -/
theorem reply4With_projects {E F : Type} (ρ : E → Option F)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (xmit' : Nat → Nat → List Packet → Nat → PrefixM F Int)
    (hx : ∀ family addr pkts mtu, ProjectsPrefix ρ id
      (xmit family addr pkts mtu) (xmit' family addr pkts mtu))
    (dst : Nat) (bytes : List UInt8) :
    ProjectsPrefix ρ id (reply4With xmit dst bytes) (reply4With xmit' dst bytes) := by
  unfold reply4With
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact hx _ _ _ _
    | exact projectsPrefix_lift ρ _
    | exact projectsPrefix_pure ρ id _
    | apply projectsPrefix_bind ρ id id
    | apply projectsPrefix_ite
    | maintenance_intro
    | dsimp only [id]
    | split

theorem receive4With_projects {E F : Type} (ρ : E → Option F)
    (reply : Nat → List UInt8 → PrefixM E Unit)
    (reply' : Nat → List UInt8 → PrefixM F Unit)
    (hr : ∀ dst bytes, ProjectsPrefix ρ id (reply dst bytes) (reply' dst bytes))
    (pkt : List UInt8) :
    ProjectsPrefix ρ id (receive4With reply pkt) (receive4With reply' pkt) := by
  unfold receive4With
  repeat' first
    | with_reducible exact hr _ _
    | exact projectsPrefix_lift ρ _
    | exact projectsPrefix_pure ρ id _
    | with_reducible exact stack_projects_failure ρ (Stack.excluded _) (stackExcluded_failure _) _ _
    | with_reducible exact stack_projects_failure ρ (invariant _) (fun _ => ⟨_,rfl⟩) _ _
    | with_reducible exact stack_projects_failure ρ (unsupported _) (fun _ => ⟨_,rfl⟩) _ _
    | apply projectsPrefix_ite
    | apply projectsPrefix_bind ρ id id
    | maintenance_intro
    | dsimp only [id]
    | split

theorem stackReceiveWith_projects {E F : Type} (ρ : E → Option F)
    (receive4 : List UInt8 → PrefixM E Unit) (receive4' : List UInt8 → PrefixM F Unit)
    (hr : ∀ pkt, ProjectsPrefix ρ id (receive4 pkt) (receive4' pkt))
    (pkt : List UInt8) :
    ProjectsPrefix ρ id (stackReceiveWith receive4 pkt) (stackReceiveWith receive4' pkt) := by
  unfold stackReceiveWith
  dsimp only
  split
  · exact hr pkt
  · split <;> exact projectsPrefix_lift ρ _

/-- The source leaves use their existing product-store frames. The TX callback
remains arbitrary and supplies its own normal-state and failed-prefix contract. -/
theorem reply4With_preserves {E : Type} {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (hx : ∀ family addr pkts mtu, PrefixPreserves I S (xmit family addr pkts mtu))
    (dst : Nat) (bytes : List UInt8) : PrefixPreserves I S (reply4With xmit dst bytes) := by
  have ambient {α : Type} (a : AmbientM α) : PrefixPreserves I S (liftPrefix (liftAmbient a)) :=
    viewLiftPrefix_preserves productStoreView safe store
      (fun state => productAmbient_spec a (fun w => productStoreView w = state) (fun _ _ hi => hi))
  have routing {α : Type} (a : Net.M α) :
      PrefixPreserves I S (liftPrefix (liftWG (liftRouting a))) :=
    viewLiftPrefix_preserves productStoreView safe store
      (liftWG_sameProductStore _ (liftRouting_sameWGStore a))
  have dev : PrefixPreserves I S (liftPrefix (liftWG getDev)) :=
    viewLiftPrefix_preserves productStoreView safe store (fun state => productGetDev_spec (fun s => s = state))
  unfold reply4With
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact hx _ _ _ _
    | with_reducible exact ambient (AmbientM.skipCut _)
    | with_reducible exact ambient (AmbientM.unsupported _)
    | with_reducible exact dev
    | with_reducible exact routing _
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | maintenance_intro
    | dsimp only
    | split
  all_goals first
    | exact ambient (AmbientM.skipCut _)
    | exact ambient (AmbientM.unsupported _)

theorem receive4With_preserves {E : Type} {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (reply : Nat → List UInt8 → PrefixM E Unit)
    (hr : ∀ dst bytes, PrefixPreserves I S (reply dst bytes))
    (pkt : List UInt8) : PrefixPreserves I S (receive4With reply pkt) := by
  have routing {α : Type} (a : Net.M α) :
      PrefixPreserves I S (liftPrefix (liftWG (liftRouting a))) :=
    viewLiftPrefix_preserves productStoreView safe store
      (liftWG_sameProductStore _ (liftRouting_sameWGStore a))
  have read : PrefixPreserves I S (liftPrefix (getWG : Leanux.M WGWorld)) :=
    viewLiftPrefix_preserves productStoreView safe store (fun state => productGetWG_spec (fun s => s = state))
  have write (f : EnvWorld → EnvWorld) : PrefixPreserves I S (liftPrefix (modifyEnv f)) := by
    apply viewLiftPrefix_preserves productStoreView safe store
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  unfold receive4With
  repeat' first
    | with_reducible exact hr _ _
    | with_reducible exact PrefixPreserves.lift_failure_bind safe (Stack.excluded _) (stackExcluded_failure _) _
    | with_reducible exact PrefixPreserves.lift_failure_bind safe (invariant _) (fun _ => ⟨_,rfl⟩) _
    | with_reducible exact PrefixPreserves.lift_failure_bind safe (unsupported _) (fun _ => ⟨_,rfl⟩) _
    | with_reducible exact read
    | with_reducible exact write _
    | with_reducible exact routing _
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.ite
    | with_reducible apply PrefixPreserves.bind
    | maintenance_intro
    | dsimp only
    | split

theorem stackReceiveWith_preserves {E : Type} {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (receive4 : List UInt8 → PrefixM E Unit)
    (hr : ∀ pkt, PrefixPreserves I S (receive4 pkt))
    (pkt : List UInt8) : PrefixPreserves I S (stackReceiveWith receive4 pkt) := by
  unfold stackReceiveWith
  dsimp only
  split
  · exact hr pkt
  · split
    · exact viewLiftPrefix_preserves productStoreView safe store (stackReceive6_sameKernel pkt)
    · exact PrefixEnsures.lift (Q := fun _ => I) _ safe (by intro h w x v hi run; cases run)

private theorem stack_appends_true {E α : Type} (a : PrefixM E α) (ha : Appends a) :
    PrefixPreserves (fun _ _ => True) (fun _ => True) a := by
  intro w h _
  obtain ⟨suffix,hs⟩ := ha w h
  refine ⟨suffix,hs,True.intro,?_⟩
  cases (runPrefix a w h).1 <;> trivial

/-- The wrappers append exactly when their actual callbacks append, with no
normal-return or history-independence restriction. -/
theorem reply4With_appends {E : Type}
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (hx : ∀ family addr pkts mtu, Appends (xmit family addr pkts mtu))
    (dst : Nat) (bytes : List UInt8) : Appends (reply4With xmit dst bytes) := by
  have checked := reply4With_preserves (I := fun _ _ => True) (S := fun _ => True)
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) xmit
    (fun family addr pkts mtu => stack_appends_true _ (hx family addr pkts mtu)) dst bytes
  intro w h
  obtain ⟨suffix,hs,_,_⟩ := checked w h True.intro
  exact ⟨suffix,hs⟩

theorem receive4With_appends {E : Type}
    (reply : Nat → List UInt8 → PrefixM E Unit)
    (hr : ∀ dst bytes, Appends (reply dst bytes))
    (pkt : List UInt8) : Appends (receive4With reply pkt) := by
  have checked := receive4With_preserves (I := fun _ _ => True) (S := fun _ => True)
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) reply
    (fun dst bytes => stack_appends_true _ (hr dst bytes)) pkt
  intro w h
  obtain ⟨suffix,hs,_,_⟩ := checked w h True.intro
  exact ⟨suffix,hs⟩

theorem stackReceiveWith_appends {E : Type}
    (receive4 : List UInt8 → PrefixM E Unit)
    (hr : ∀ pkt, Appends (receive4 pkt)) (pkt : List UInt8) : Appends (stackReceiveWith receive4 pkt) := by
  have checked := stackReceiveWith_preserves (I := fun _ _ => True) (S := fun _ => True)
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) receive4
    (fun pkt => stack_appends_true _ (hr pkt)) pkt
  intro w h
  obtain ⟨suffix,hs,_,_⟩ := checked w h True.intro
  exact ⟨suffix,hs⟩

end Leanux.Proofs.WG.Lifetimes
