import PairExcept

namespace Binary.Pair

/-- An assertion whose failing arm ends the Except computation immediately.
Keeping the continuation outside the guard avoids duplicating it in reduction. -/
def require (condition : Bool) (error : String) : Except String Unit :=
  if condition then .ok () else .error error

theorem require_bind_eq (condition : Bool) (error : String) (rest : Except String α) :
    (require condition error >>= fun _ => rest)=(do
      unless condition do throw error
      rest) := by
  cases condition <;> rfl

theorem require_ok {condition : Bool} {error : String} (run : require condition error=.ok ()) :
    condition=true := by
  cases condition with
  | false => cases run
  | true => rfl

theorem require_bind_ok (condition : Bool) (error : String) (rest : Except String α) (value : α)
    (run : (require condition error >>= fun _ => rest)=.ok value) :
    condition=true ∧ rest=.ok value := by
  cases condition with
  | false => cases run
  | true => exact ⟨rfl,run⟩

end Binary.Pair
