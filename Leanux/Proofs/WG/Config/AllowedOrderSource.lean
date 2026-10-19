import Leanux.Proofs.WG.Config.RemainingLoopSource
import Leanux.Proofs.WG.Config.AllowedOrderEffects
import Leanux.Proofs.WG.Config.ScalarPrefixSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.AllowedOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise
open Leanux.Proofs.Framing Lifetimes Std.Do

theorem finish_value (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Ensures (peerTailFinishSource attrs peer pid ret) (fun _=>True) (fun value _=>value=ret) := by
  have factor : peerTailFinishSource attrs peer pid ret =
      (do let _ ← peerTailFinishSource attrs peer pid 0; pure ret) := by
    simp only [peerTailFinishSource,bind_assoc,Leanux.Proofs.WG.Queues.TxDisposition.bind_ite,pure_bind]
  intro w a value v b _ run
  rw [factor] at run
  change ((((peerTailFinishSource attrs peer pid 0).run w).run a) >>= fun ((_,u),c) =>
    Except.ok ((ret,u),c)) = Except.ok ((value,v),b) at run
  cases earlier : ((peerTailFinishSource attrs peer pid 0).run w).run a with
  | error stop => rw [earlier] at run; cases run
  | ok out =>
    obtain ⟨⟨ignored,u⟩,c⟩ := out
    rw [earlier] at run
    cases run
    rfl


abbrev HistorySpec {α : Type} (P S : List RoutingCompletion → Prop)
    (a : WGPrefix RoutingCompletion α) (Q : α → List RoutingCompletion → Prop) :=
  StatePrefixEnsures (fun h _ _=>P h) S a (fun ret h _ _=>Q ret h)

def mark (site : Decision) (value : Bool) : WGPrefix RoutingCompletion Unit :=
  liftWGPrefix (do let _ ← branch site value; pure ())

theorem branch_factor (site : Decision) (value : Bool) :
    (liftWGPrefix (branch site value) : WGPrefix RoutingCompletion Bool) =
      (do mark site value; pure value) := rfl

theorem quiet {α : Type} (action : WG.M α) (P S : List RoutingCompletion → Prop)
    (safe : ∀h,P h→S h) :
    HistorySpec P S (liftWGPrefix action) (fun _ h=>P h) :=
  StatePrefixEnsures.lift action (fun h _ _ point=>safe h point)
    (fun _ _ _ _ _ _ point _=>point)

theorem mark_then {α : Type} (site : Decision) (value : Bool)
    {P S : List RoutingCompletion → Prop} {Q : α → List RoutingCompletion → Prop}
    {action : WGPrefix RoutingCompletion α} (safe : ∀h,P h→S h)
    (next : HistorySpec P S action Q) :
    HistorySpec P S (do mark site value; action) Q :=
  StatePrefixEnsures.bind (quiet _ P S safe) (fun _=>next)

theorem lifted_value (action : WG.M Int) (ret : Int)
    (same : Ensures action (fun _=>True) (fun value _=>value=ret))
    (P S : List RoutingCompletion → Prop) (safe : ∀h,P h→S h) :
    HistorySpec P S (liftWGPrefix action) (fun value h=>value=ret ∧ P h) :=
  StatePrefixEnsures.lift action (fun h _ _ point=>safe h point)
    (fun _ w a value v b point run=>⟨same w a value v b trivial run,point⟩)

theorem out_rule (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int)
    (P S : List RoutingCompletion → Prop) (safe : ∀h,P h→S h) :
    HistorySpec P S (peerConfigOutObserved attrs peer ret) (fun value h=>value=ret ∧ P h) := by
  unfold peerConfigOutObserved
  apply StatePrefixEnsures.bind (quiet _ P S safe)
  intro _
  apply StatePrefixEnsures.bind (quiet _ P S safe)
  intro _
  exact StatePrefixEnsures.pure ret (fun h _ _ point=>safe h point) (fun _ _ _ point=>⟨rfl,point⟩)

def body (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (entry : AllowedIpEntry) (acc : Option Int × Int) :
    WGPrefix RoutingCompletion (ForInStep (Option Int × Int)) := do
  mark .peerAipsIter true
  match entry with
  | .malformed =>
    mark .peerAipParseErr true
    let ret ← peerConfigOutObserved attrs peer (-EINVAL)
    pure (.done (some ret,acc.2))
  | .attrs ip =>
    mark .peerAipParseErr false
    let ret ← completedAllowedip pid ip
    mark .peerAipErr (ret<0)
    if ret<0 then
      let result ← peerConfigOutObserved attrs peer ret
      pure (.done (some result,ret))
    else pure (.yield (none,ret))

theorem tail_factor (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    peerConfigTailObserved attrs peer pid = (do
      mark .peerHasAips attrs.allowedIps.isSome
      if attrs.allowedIps.isSome then
        let acc ← forIn (attrs.allowedIps.getD []) (none,0) (body attrs peer pid)
        match acc.1 with
        | some ret => pure ret
        | none =>
          mark .peerAipsIter false
          liftWGPrefix (peerTailFinishSource attrs peer pid acc.2)
      else liftWGPrefix (peerTailFinishSource attrs peer pid 0)) := by
  unfold peerConfigTailObserved peerAllowedIpsObservedWG peerAllowedIpsObservedWith
    peerAllowedIpsWith body
  simp only [branch_factor,bind_assoc,pure_bind,decide_eq_true_eq]
  congr 1
  funext u
  split
  · congr 1
    funext acc
    rcases acc with ⟨ret,last⟩
    cases ret <;> rfl
  · rfl

theorem completed_rule (pid : PeerId) (ip : AllowedIpAttrs)
    {P S : List RoutingCompletion → Prop} {Q : Int → List RoutingCompletion → Prop}
    (safe : ∀h,P h→S h)
    (emitted : ∀ h e ret,P h→e.call=.allowedIp pid ip ret→S (h++[e])∧Q ret (h++[e])) :
    HistorySpec P S (completedAllowedip pid ip) Q := by
  intro w a h point
  have observed := completedAllowedip_run pid ip w a h
  dsimp only [runWGPrefix,runStatePrefix] at observed
  rw [observed]
  cases run : ((setAllowedip pid ip).run w).run a with
  | error stop => exact ⟨[],by simp,safe h point,trivial⟩
  | ok out =>
    obtain ⟨⟨ret,v⟩,b⟩:=out
    exact ⟨[⟨.allowedIp pid ip ret,routingView w,routingView v⟩],rfl,
      emitted h _ ret point rfl⟩

theorem record_allowed_rule (pid : PeerId)
    (input rest : List AllowedIpEntry) (ip : AllowedIpAttrs)
    (before : List RoutingCompletion) (acc : Option Int × Int) :
    HistorySpec (At pid input (.attrs ip::rest) before acc) (Safe pid input before)
      (completedAllowedip pid ip) (After pid input ip rest before) := by
  apply completed_rule
  · exact fun _ point=>point.safe
  · intro h e ret point call
    obtain ⟨_,prior,eq,path⟩:=point
    have next : After pid input ip rest before ret (h++[e]) :=
      ⟨prior,acc.2,e,by simp only [eq,List.append_assoc],path,call⟩
    exact ⟨next.safe,next⟩

theorem body_spec (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (input rest : List AllowedIpEntry) (entry : AllowedIpEntry)
    (before : List RoutingCompletion) (acc : Option Int × Int) :
    HistorySpec (At pid input (entry::rest) before acc) (Safe pid input before)
      (body attrs peer pid entry acc)
      (fun step=>match step with
        | .done acc=>Done pid input before acc
        | .yield acc=>At pid input rest before acc) := by
  unfold body
  apply mark_then _ _ (fun _ point=>point.safe)
  cases entry with
  | malformed =>
    apply mark_then _ _ (fun _ point=>point.safe)
    apply StatePrefixEnsures.bind (out_rule attrs peer (-EINVAL) _ _ (fun _ point=>point.safe))
    intro ret
    apply StatePrefixEnsures.pure (show ForInStep (Option Int × Int) from .done (some ret,acc.2))
    · exact fun _ _ _ point=>point.2.safe
    · intro h _ _ point
      obtain ⟨result,_,added,eq,path⟩:=point
      exact ⟨added,eq,Or.inr (Or.inl ⟨result,rest,acc.2,path⟩)⟩
  | attrs ip =>
    apply mark_then _ _ (fun _ point=>point.safe)
    apply StatePrefixEnsures.bind (record_allowed_rule pid input rest ip before acc)
    intro ret
    apply mark_then _ _ (fun _ point=>point.safe)
    split
    · rename_i negative
      apply StatePrefixEnsures.bind (out_rule attrs peer ret _ _ (fun _ point=>point.safe))
      intro same
      apply StatePrefixEnsures.pure (show ForInStep (Option Int × Int) from .done (some same,ret))
      · exact fun _ _ _ point=>point.2.safe
      · intro h _ _ point
        obtain ⟨rfl,point⟩:=point
        exact point.negative negative
    · rename_i nonnegative
      apply StatePrefixEnsures.pure (show ForInStep (Option Int × Int) from .yield (none,ret))
      · exact fun _ _ _ point=>point.safe
      · exact fun _ _ _ point=>point.nonnegative nonnegative

theorem loop_spec (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (input rest : List AllowedIpEntry) (before : List RoutingCompletion)
    (acc : Option Int × Int) :
    HistorySpec (At pid input rest before acc) (Safe pid input before)
      (forIn rest acc (body attrs peer pid)) (Done pid input before) := by
  apply Config.RemainingLoop.forIn_remaining rest acc (body attrs peer pid)
    (fun rest acc h _ _=>At pid input rest before acc h)
  · exact fun _ _ _ _ point=>point.safe
  · intro acc h _ _ point
    obtain ⟨none,added,eq,path⟩:=point
    exact ⟨⟨added,eq,Or.inl ⟨[],acc.2,path⟩⟩,added,eq,by simpa only [none] using path⟩
  · intro entry tail acc
    exact (body_spec attrs peer pid input tail entry before acc).consequence
      (fun _ _ _ point=>point) (fun step _ _ _ point=>by cases step <;> exact point)

theorem tail_spec (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (before : List RoutingCompletion) :
    HistorySpec (fun h=>h=before) (Safe pid (attrs.allowedIps.getD []) before)
      (peerConfigTailObserved attrs peer pid)
      (fun ret h=>∃added,h=before++added∧Finished pid (attrs.allowedIps.getD []) added ret) := by
  rw [tail_factor]
  have initial : ∀h,h=before→Safe pid (attrs.allowedIps.getD []) before h := by
    intro h eq
    exact ⟨[],by simpa using eq,Or.inl ⟨attrs.allowedIps.getD [],0,.nil⟩⟩
  apply mark_then _ _ initial
  split
  · have enter : HistorySpec (fun h=>h=before) (Safe pid (attrs.allowedIps.getD []) before)
        (forIn (attrs.allowedIps.getD []) (none,0) (body attrs peer pid))
        (Done pid (attrs.allowedIps.getD []) before) :=
      (loop_spec attrs peer pid (attrs.allowedIps.getD []) (attrs.allowedIps.getD []) before (none,0)).consequence
        (fun h _ _ eq=>⟨rfl,[],by simpa using eq,.nil⟩)
        (fun _ _ _ _ point=>point)
    apply StatePrefixEnsures.bind enter
    intro acc
    cases result : acc.1 with
    | some ret =>
      apply StatePrefixEnsures.pure ret
      · exact fun _ _ _ point=>point.safe
      · intro h _ _ point
        obtain ⟨added,eq,finish⟩:=point
        exact ⟨added,eq,by simpa only [result] using finish⟩
    | none =>
      apply mark_then _ _ (fun _ point=>point.safe)
      apply (lifted_value _ acc.2 (finish_value attrs peer pid acc.2)
        (Done pid (attrs.allowedIps.getD []) before acc)
        (Safe pid (attrs.allowedIps.getD []) before) (fun _ point=>point.safe)).consequence
        (fun _ _ _ point=>point)
      intro ret h _ _ point
      obtain ⟨rfl,added,eq,finish⟩:=point
      exact ⟨added,eq,Or.inl (by simpa only [result] using finish)⟩
  · rename_i missing
    have empty : attrs.allowedIps.getD []=[] := by
      cases h:attrs.allowedIps with
      | none=>rfl
      | some ips=>simp only [h,Option.isSome_some] at missing;contradiction
    apply (lifted_value _ 0 (finish_value attrs peer pid 0) _ _ initial).consequence
      (fun _ _ _ eq=>eq)
    intro ret h _ _ point
    obtain ⟨rfl,rfl⟩:=point
    exact ⟨[],by simp,Or.inl (by rw [empty];exact .nil)⟩

theorem completed_remove_rule (pid : PeerId)
    {P S Q : List RoutingCompletion→Prop}
    (safe : ∀h,P h→S h)
    (emitted : ∀h e,P h→e.call=.removePeer pid→S (h++[e])∧Q (h++[e])) :
    HistorySpec P S (completedRemovePeer pid) (fun _=>Q) := by
  intro w a h point
  have observed:=completedRemovePeer_run pid w a h
  dsimp only [runWGPrefix,runStatePrefix] at observed
  rw [observed]
  cases run : ((removeByPeer pid).run w).run a with
  | error stop=>exact ⟨[],by simp,safe h point,trivial⟩
  | ok out=>
    obtain ⟨⟨ret,v⟩,b⟩:=out
    exact ⟨[⟨.removePeer pid,routingView w,routingView v⟩],rfl,
      emitted h _ point rfl⟩

theorem history_transport {α : Type}
    {P S : List RoutingCompletion→Prop} {Q : α→List RoutingCompletion→Prop}
    {P' S' : List RoutingCompletion→Prop} {Q' : α→List RoutingCompletion→Prop}
    {action : WGPrefix RoutingCompletion α}
    (given : HistorySpec P S action Q)
    (pre : ∀h,P' h→P h) (safe : ∀h,S h→S' h)
    (post : ∀x h,Q x h→Q' x h) : HistorySpec P' S' action Q' := by
  intro w a h hi
  obtain ⟨added,eq,hs,hq⟩:=given w a h (pre h hi)
  refine ⟨added,eq,safe _ hs,?_⟩
  cases outcome : (runPrefix (StateT.run action w) a h).1 with
  | error stop=>trivial
  | ok value=>
    simp only [outcome] at hq ⊢
    exact post _ _ hq

theorem removal_spec (peer : Option PeerId) (before : List RoutingCompletion) :
    HistorySpec (fun h=>h=before) (Segment (RemovalPartial peer) before)
      (peerRemoveObserved peer) (fun _=>Segment (Removal peer) before) := by
  have empty : ∀h,h=before→Segment (RemovalPartial peer) before h :=
    fun h eq=>⟨[],by simpa using eq,Or.inl rfl⟩
  unfold peerRemoveObserved
  rw [branch_factor]
  simp only [bind_assoc,pure_bind]
  apply mark_then _ _ empty
  cases peer with
  | none=>
    simp only [Option.isNone_none,ite_true]
    exact StatePrefixEnsures.pure () (fun h _ _ eq=>empty h eq)
      (fun h _ _ eq=>⟨[],by simpa using eq,rfl⟩)
  | some pid=>
    simp only [Option.isNone_some,Bool.false_eq_true,ite_false]
    have finalSafe : ∀h,Segment (Removal (some pid)) before h→
        Segment (RemovalPartial (some pid)) before h := by
      intro h point
      obtain ⟨events,eq,point⟩:=point
      exact ⟨events,eq,Or.inr point⟩
    unfold peerMakeDeadObserved
    simp only [bind_assoc]
    apply StatePrefixEnsures.bind (quiet _ _ _ empty)
    intro _
    apply StatePrefixEnsures.bind (completed_remove_rule pid empty ?_)
    · intro _
      repeat' first
        | exact quiet _ _ _ finalSafe
        | apply StatePrefixEnsures.bind (quiet _ _ _ finalSafe)
        | intro x
    · intro h e eq call
      have point : Segment (Removal (some pid)) before (h++[e]) :=
        ⟨[e],by rw[eq],e,call,rfl⟩
      exact ⟨finalSafe _ point,point⟩

theorem tail_started (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (pid : PeerId) (before : List RoutingCompletion)
    (keep : ¬(flags &&& WGPEER_F_REMOVE_ME != 0)=true) :
    HistorySpec
      (Segment (Front (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) pid) before)
      (Segment (UpdatePartial attrs peer flags pid) before)
      (peerConfigTailObserved attrs peer pid)
      (fun ret=>Segment (fun events=>UpdateFinished attrs peer flags pid events ret) before) := by
  intro w a h point
  obtain ⟨front,eq,hf⟩:=point
  obtain ⟨suffix,hs,safe,post⟩:=tail_spec attrs peer pid h w a h rfl
  have join (added : List RoutingCompletion) {result : List RoutingCompletion}
      (equal : result=h++added) : result=before++(front++added) := by
    rw[equal,eq,List.append_assoc]
  refine ⟨suffix,hs,?_,?_⟩
  · obtain ⟨added,equal,point⟩:=safe
    refine ⟨front++added,join added equal,?_⟩
    simp only [UpdatePartial,keep]
    exact Or.inr ⟨front,added,hf,point,rfl⟩
  · cases outcome : (runPrefix (StateT.run (peerConfigTailObserved attrs peer pid) w) a h).1 with
    | error stop=>trivial
    | ok value=>
      obtain ⟨⟨ret,v⟩,b⟩:=value
      simp only [outcome] at post ⊢
      obtain ⟨added,equal,point⟩:=post
      refine ⟨front++added,join added equal,?_⟩
      simp only [UpdateFinished,keep]
      exact ⟨front,added,hf,point,rfl⟩

theorem lift_bind {α β : Type} (a : WG.M α) (f : α→WG.M β) :
    (liftWGPrefix (a>>=f) : WGPrefix RoutingCompletion β) =
      (do let x←liftWGPrefix a;liftWGPrefix (f x)) := by
  funext w ambient h
  change runStatePrefix (liftWGPrefix (a>>=f)) w ambient h =
    runStatePrefix (do let x←liftWGPrefix a;liftWGPrefix (f x)) w ambient h
  simp only [liftWGPrefix,runStatePrefix_bind,runStatePrefix_lift,StateT.run_bind]
  cases run:((a.run w).run ambient) <;> rfl

theorem lift_pure {α : Type} (x : α) :
    (liftWGPrefix (pure x) : WGPrefix RoutingCompletion α)=pure x := rfl

theorem lift_ite {α : Type} (c : Prop) [Decidable c] (a b : WG.M α) :
    (liftWGPrefix (if c then a else b) : WGPrefix RoutingCompletion α)=
      (if c then liftWGPrefix a else liftWGPrefix b) := by split <;> rfl

theorem update_factor (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    peerConfigUpdateObserved attrs peer flags psk pid = (do
      mark .peerRemoveMe (flags &&& WGPEER_F_REMOVE_ME != 0)
      if flags &&& WGPEER_F_REMOVE_ME != 0 then
        peerRemoveObserved peer
        peerConfigOutObserved attrs peer 0
      else
        liftWGPrefix (ScalarPrefix.scalarPrefix attrs psk pid)
        mark .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)
        if flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0 then completedRemovePeer pid
        peerConfigTailObserved attrs peer pid) := by
  cases ep:attrs.endpoint <;>
    simp only [peerConfigUpdateObserved,ScalarPrefix.scalarPrefix,ScalarPrefix.pskSource,
      ScalarPrefix.endpointSource,endpointAttributeUpdate,ep,lift_bind,lift_ite,lift_pure,
      branch_factor,bind_assoc,Leanux.Proofs.WG.Queues.TxDisposition.bind_ite,pure_bind]

theorem replacement_tail_spec (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (pid : PeerId) (before : List RoutingCompletion)
    (keep : ¬(flags &&& WGPEER_F_REMOVE_ME != 0)=true) :
    HistorySpec (fun h=>h=before) (Segment (UpdatePartial attrs peer flags pid) before)
      (do
        mark .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)
        if flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0 then completedRemovePeer pid
        peerConfigTailObserved attrs peer pid)
      (fun ret=>Segment (fun events=>UpdateFinished attrs peer flags pid events ret) before) := by
  have initial : ∀h,h=before→Segment (UpdatePartial attrs peer flags pid) before h :=
    fun h eq=>⟨[],by simpa using eq,UpdatePartial.empty attrs peer flags pid⟩
  apply mark_then _ _ initial
  split
  · rename_i replace
    apply StatePrefixEnsures.bind (completed_remove_rule pid initial ?_)
    · intro _
      exact tail_started attrs peer flags pid before keep
    · intro h e eq call
      have hf : Front (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) pid [e] := by
        simp only [Front,replace,ite_true]
        exact ⟨e,call,rfl⟩
      have point : Segment (Front (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) pid) before (h++[e]) :=
        ⟨[e],by rw[eq],hf⟩
      refine ⟨?_,point⟩
      refine ⟨[e],by rw[eq],?_⟩
      simp only [UpdatePartial,keep]
      exact Or.inr ⟨[e],[],hf,Or.inl ⟨attrs.allowedIps.getD [],0,.nil⟩,by simp⟩
  · rename_i missing
    apply (tail_started attrs peer flags pid before keep).consequence
    · intro h _ _ eq
      refine ⟨[],by simpa using eq,?_⟩
      simp only [Front,missing,Bool.false_eq_true,ite_false]
    · exact fun _ _ _ _ point=>point

theorem update_spec (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (before : List RoutingCompletion) :
    HistorySpec (fun h=>h=before) (Segment (UpdatePartial attrs peer flags pid) before)
      (peerConfigUpdateObserved attrs peer flags psk pid)
      (fun ret=>Segment (fun events=>UpdateFinished attrs peer flags pid events ret) before) := by
  have initial : ∀h,h=before→Segment (UpdatePartial attrs peer flags pid) before h :=
    fun h eq=>⟨[],by simpa using eq,UpdatePartial.empty attrs peer flags pid⟩
  rw [update_factor]
  apply mark_then _ _ initial
  split
  · rename_i remove
    have rem : HistorySpec (fun h=>h=before) (Segment (UpdatePartial attrs peer flags pid) before)
        (peerRemoveObserved peer) (fun _=>Segment (Removal peer) before) :=
      history_transport (removal_spec peer before)
      (fun _ eq=>eq)
      (fun h point=>by
        obtain ⟨events,eq,hp⟩:=point
        exact ⟨events,eq,by simpa only [UpdatePartial,remove,ite_true] using hp⟩)
      (fun _ _ point=>point)
    apply StatePrefixEnsures.bind rem
    intro _
    have remSafe : ∀h,Segment (Removal peer) before h→
        Segment (UpdatePartial attrs peer flags pid) before h := by
      intro h point
      obtain ⟨events,eq,hp⟩:=point
      exact ⟨events,eq,by simp only [UpdatePartial,remove,ite_true];exact Or.inr hp⟩
    apply (out_rule attrs peer 0 (Segment (Removal peer) before)
      (Segment (UpdatePartial attrs peer flags pid) before) remSafe).consequence
      (fun _ _ _ point=>point)
    intro ret h _ _ point
    obtain ⟨same,events,eq,hp⟩:=point
    exact ⟨events,eq,by simp only [UpdateFinished,remove,ite_true];exact ⟨same,hp⟩⟩
  · rename_i keep
    apply StatePrefixEnsures.bind (quiet _ _ _ initial)
    intro _
    exact replacement_tail_spec attrs peer flags pid before keep

end Leanux.Proofs.WG.Config.AllowedOrder
