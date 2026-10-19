import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationFreeCut

/-! Actual disposal walks retain completed frees and an exact stopped local
suffix. The same incoming tickets are partitioned without relabelling them. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.FreeFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues AuthenticatedEffects

def walk (free : SkbId → PrefixM E Unit) (item : List SkbId) : PrefixM E Unit :=
  forIn item () fun skb _ => do free skb; pure (.yield ())

theorem walk_nil (free : SkbId → PrefixM E Unit) : walk free [] = pure () := rfl

theorem walk_cons (free : SkbId → PrefixM E Unit) (skb : SkbId) (item : List SkbId) :
    walk free (skb :: item) = (do free skb; walk free item) := by
  simp only [walk,List.forIn_cons,bind_assoc,pure_bind]

inductive Steps (free : SkbId → PrefixM E Unit) :
    List SkbId → World → List E → World → List E → Prop
  | nil : Steps free [] w h w h
  | cons {skb : SkbId} (run : runPrefix (free skb) w h = (.ok ((),v),tail))
      (rest : Steps free item v tail last history) :
      Steps free (skb :: item) w h last history

theorem Steps.run {free : SkbId → PrefixM E Unit} (steps : Steps free item w h v tail) :
    runPrefix (walk free item) w h = (.ok ((),v),tail) := by
  induction steps with
  | nil => rfl
  | cons first _ ih => rw [walk_cons,runPrefix_bind,first]; exact ih

theorem walk_normal (free : SkbId → PrefixM E Unit) (item : List SkbId)
    (w v : World) (h tail : List E)
    (run : runPrefix (walk free item) w h = (.ok ((),v),tail)) :
    Steps free item w h v tail := by
  induction item generalizing w h with
  | nil =>
    simp only [walk_nil,runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at run
    obtain ⟨⟨_,rfl⟩,rfl⟩ := run
    exact .nil
  | cons skb item ih =>
    rw [walk_cons,runPrefix_bind] at run
    cases first : runPrefix (free skb) w h with
    | mk result history =>
      cases result with
      | error stop => simp [first] at run
      | ok out =>
        rcases out with ⟨⟨⟩,middle⟩
        simp only [first] at run
        exact .cons first (ih middle history run)

theorem walk_stopped (free : SkbId → PrefixM E Unit) (item : List SkbId)
    (w : World) (h tail : List E) (stop : Stop)
    (run : runPrefix (walk free item) w h = (.error stop,tail)) :
    ∃ done skb remaining middle history,
      item = done ++ skb :: remaining ∧
      Steps free done w h middle history ∧
      runPrefix (free skb) middle history = (.error stop,tail) := by
  induction item generalizing w h with
  | nil => simp [walk_nil] at run
  | cons skb item ih =>
    rw [walk_cons,runPrefix_bind] at run
    cases first : runPrefix (free skb) w h with
    | mk result history =>
      cases result with
      | error failed =>
        simp only [first,Prod.mk.injEq,Except.error.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        exact ⟨[],skb,item,w,h,rfl,.nil,first⟩
      | ok out =>
        rcases out with ⟨⟨⟩,middle⟩
        simp only [first] at run
        obtain ⟨done,current,remaining,last,events,split,steps,failed⟩ := ih middle history run
        exact ⟨skb :: done,current,remaining,last,events,
          by simp only [split,List.cons_append],.cons first steps,failed⟩


def repay (o : StagedDisposal.TxSource.Ops E) (pid : PeerId) (key : KeypairId) : PrefixM E Bool := do
  o.access (keypairPutPrefix (some key) false)
  o.release (some pid)
  return true

theorem dispose_factor (o : StagedDisposal.TxSource.Ops E) (free : SkbId → PrefixM E Unit)
    (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    Terminal.disposeWith o free pid item key = (do walk free item; repay o pid key) := rfl

/-- A stopped DEAD disposal either has an exact unvisited free suffix, or
all frees completed before reference repayment stopped. No missing packet is
classified as a drop solely from the returned state. -/
inductive Stopped (o : StagedDisposal.TxSource.Ops E) (free : SkbId → PrefixM E Unit)
    (pid : PeerId) (item : List SkbId) (key : KeypairId)
    (w : World) (h : List E) (stop : Stop) (tail : List E) : Prop
  | current {skb : SkbId} (split : item = done ++ skb :: remaining)
      (steps : Steps free done w h middle history)
      (run : runPrefix (free skb) middle history = (.error stop,tail)) :
      Stopped o free pid item key w h stop tail
  | repayment (steps : Steps free item w h middle history)
      (run : runPrefix (repay o pid key) middle history = (.error stop,tail)) :
      Stopped o free pid item key w h stop tail

theorem dispose_stopped (o : StagedDisposal.TxSource.Ops E) (free : SkbId → PrefixM E Unit)
    (pid : PeerId) (item : List SkbId) (key : KeypairId)
    (w : World) (h tail : List E) (stop : Stop)
    (run : runPrefix (Terminal.disposeWith o free pid item key) w h = (.error stop,tail)) :
    Stopped o free pid item key w h stop tail := by
  rw [dispose_factor,runPrefix_bind] at run
  cases walkRun : runPrefix (walk free item) w h with
  | mk result history =>
    cases result with
    | error failed =>
      simp only [walkRun,Prod.mk.injEq,Except.error.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      obtain ⟨done,skb,remaining,middle,events,split,steps,failed⟩ :=
        walk_stopped free item w h _ _ walkRun
      exact .current split steps failed
    | ok out =>
      rcases out with ⟨⟨⟩,middle⟩
      simp only [walkRun] at run
      exact .repayment (walk_normal free item w middle h history walkRun) run

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.FreeFrontier
