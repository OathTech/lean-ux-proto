import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointCuts

/-! A source point keeps the same ownership projection, including the native
mutation before its receipt. The write requirements remain in Framed until
its canonical caller derives them. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.Proofs.Logged

variable {E α : Type} {action remaining : WGPrefix E α} {shape : Shape action}
variable {w v : WGWorld} {a b : Ambient} {h middle : List E} {site : Site}

theorem Point.view (point : Point shape w a h site v b middle remaining)
    (framed : Framed shape w a h) : StagedEntry.view v=StagedEntry.view w := by
  induction point with
  | entry shape => rfl
  | returned shape performed => exact framed.normal performed
  | metadata point => exact point.frame
  | native token performed => exact token.native_frame framed performed
  | left tail point ih => exact ih framed.1
  | right head tail leading point ih =>
      exact (ih (framed.2 _ _ _ _ leading)).trans (framed.1.normal leading)
  | focus encode decode inverse point ih => exact ih framed
  | receipt record point ih => exact ih framed
  | receiptNative shape record performed => exact Framed.normal (shape:=shape) framed performed

theorem Shape.appended {E α : Type} {body : WGPrefix E α} (shape : Shape body)
    {w v : WGWorld} {a b : Ambient} {h last : List E} {value : α}
    (performed : runWGPrefix body w a h=(.ok ((value,v),b),last)) : ∃suffix,last=h++suffix := by
  obtain ⟨suffix,extended⟩:=shape.appends w a h
  change (runWGPrefix body w a h).2=_ at extended
  exact ⟨suffix,by simpa only [performed] using extended⟩

theorem Point.appends (point : Point shape w a h site v b middle remaining) :
    ∃suffix,middle=h++suffix := by
  induction point with
  | entry shape => exact ⟨[],by simp⟩
  | returned shape performed => exact shape.appended performed
  | metadata point => exact ⟨[],by simp⟩
  | native token performed => exact ⟨[],by simp⟩
  | left tail point ih => exact ih
  | right head tail leading point ih =>
      obtain ⟨suffix,extended⟩:=head.appended leading
      obtain ⟨rest,after⟩:=ih
      exact ⟨suffix++rest,by simpa only [extended,List.append_assoc] using after⟩
  | focus encode decode inverse point ih => exact ⟨_,rfl⟩
  | receipt record point ih => exact ih
  | receiptNative shape record performed => exact shape.appended performed

theorem emitMany_appends (events : List E) (value : α) : StateAppends (emitMany events value) :=
  fun _ _ _=>⟨events,rfl⟩

theorem receiptFrom_appends (w : WGWorld) (a : Ambient) (body : WGPrefix E α)
    (record : WGRunWitness α→E) (appends : StateAppends body) :
    StateAppends (receiptFrom w a body record) := by
  intro u b h
  obtain ⟨suffix,extended⟩:=appends u b h
  change (runWGPrefix body u b h).2=_ at extended
  change ∃suffix,(runWGPrefix (receiptFrom w a body record) u b h).2=h++suffix
  rw [receiptFrom_run]
  cases performed : runWGPrefix body u b h with
  | mk out last =>
      rw [performed] at extended
      cases out with
      | error reason => exact ⟨suffix,extended⟩
      | ok pair =>
          obtain ⟨⟨value,v⟩,c⟩:=pair
          change last=h++suffix at extended
          exact ⟨suffix++[record ⟨value,w,v,a,c⟩],by simpa only [extended] using List.append_assoc h suffix [record ⟨value,w,v,a,c⟩]⟩

theorem Point.remaining_appends (point : Point shape w a h site v b middle remaining) : StateAppends remaining := by
  induction point with
  | entry shape => exact shape.appends
  | returned shape performed => exact StateAppends.pure _
  | metadata point => exact PeerMetadata.prefixRemainder_appends point
  | native token performed => exact emitMany_appends _ _
  | left tail point ih => exact StateAppends.bind ih (fun value=>(tail value).appends)
  | right head tail leading point ih => exact ih
  | focus encode decode inverse point ih => exact StateAppends.focus _ _ _
  | receipt record point ih => exact receiptFrom_appends _ _ _ _ ih
  | receiptNative shape record performed => exact emitMany_appends _ _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
