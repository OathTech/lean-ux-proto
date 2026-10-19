import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPrimitiveReserveSource

/-! Reservation points include the original key getter's internal guards,
the fixed write and two existing receipt boundaries. Pending points keep the
actual incremented cell and saved native entry; every remainder is the literal
remainder of that reservation, including its saved capture before-state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staging.Points
set_option maxHeartbeats 600000

def nonceEvent (key : Keypair) : Event := .old (.nonce (Nonce.allocation (Nonce.cell key)))
def reservedEvent (kid : KeypairId) (w v : WGWorld) (a b : Ambient) (key : Keypair) : Event :=
  .old (.reserved kid ⟨key.sendingCounter,w,v,a,b⟩)

def afterRead (kid : KeypairId) (key : Keypair) : WGPrefix Event Nat := do
  liftWGPrefix (setKeypair kid {key with sendingCounter:=key.sendingCounter+1})
  emitStatePrefix (nonceEvent key)
  pure key.sendingCounter

def afterWrite (key : Keypair) : WGPrefix Event Nat := do
  emitStatePrefix (nonceEvent key)
  pure key.sendingCounter

def afterNonce (kid : KeypairId) (w v : WGWorld) (a b : Ambient) (key : Keypair) : WGPrefix Event Nat := do
  emitStatePrefix (reservedEvent kid w v a b key)
  pure key.sendingCounter

inductive ReservePoint (kid : KeypairId) (w : WGWorld) (a : Ambient) (h : List Event) :
    WGWorld → Ambient → List Event → WGPrefix Event Nat → Type 1 where
  | entry : ReservePoint kid w a h w a h (state (Journal.reserve kid))
  | reading {β : Type} {leaf : WG.M β} {rest : WG.M Keypair}
      (point : KeyPoint (readShape kid) w a leaf v b rest) :
      ReservePoint kid w a h v b h
        (savedReceipt (fun run=>.old (.reserved kid run)) w a (do
          let key←liftWGPrefix rest
          afterRead kid key))
  | read (run : ((getKeypair kid).run w).run a=.ok ((key,u),b)) :
      ReservePoint kid w a h u b h
        (savedReceipt (fun run=>.old (.reserved kid run)) w a (afterRead kid key))
  | written (read : ((getKeypair kid).run w).run a=.ok ((key,u),b))
      (write : ((setKeypair kid {key with sendingCounter:=key.sendingCounter+1}).run u).run b=.ok (((),v),c)) :
      ReservePoint kid w a h v c h
        (savedReceipt (fun run=>.old (.reserved kid run)) w a (afterWrite key))
  | nonce (read : ((getKeypair kid).run w).run a=.ok ((key,u),b))
      (write : ((setKeypair kid {key with sendingCounter:=key.sendingCounter+1}).run u).run b=.ok (((),v),c)) :
      ReservePoint kid w a h v c (h++[nonceEvent key]) (afterNonce kid w v a c key)
  | reserved (read : ((getKeypair kid).run w).run a=.ok ((key,u),b))
      (write : ((setKeypair kid {key with sendingCounter:=key.sendingCounter+1}).run u).run b=.ok (((),v),c)) :
      ReservePoint kid w a h v c ((h++[nonceEvent key])++[reservedEvent kid w v a c key]) (pure key.sendingCounter)

theorem ReservePoint.residual (point : ReservePoint kid w a h v b middle rest) :
    runWGPrefix (state (Journal.reserve kid)) w a h=runWGPrefix rest v b middle := by
  cases point with
  | entry=>rfl
  | reading point=>
    rw [reserve_factor]
    simp only [reserveObserved,reserveBody,savedReceipt,afterRead,runWGPrefix_receiptWGObserved,
      run_bind,runWGPrefix_lift,point.residual]
    rfl
  | read run=>
    rw [reserve_factor]
    simp only [reserveObserved,reserveBody,savedReceipt,runWGPrefix_receiptWGObserved,run_bind,runWGPrefix_lift,run]
    rfl
  | written read write=>
    rw [reserve_factor]
    simp only [reserveObserved,reserveBody,savedReceipt,runWGPrefix_receiptWGObserved,run_bind,runWGPrefix_lift,read,write]
    rfl
  | nonce read write=>
    rw [reserve_factor]
    simp only [reserveObserved,reserveBody,runWGPrefix_receiptWGObserved,run_bind,runWGPrefix_lift,read,write]
    rfl
  | reserved read write=>
    rw [reserve_factor]
    simp only [reserveObserved,reserveBody,runWGPrefix_receiptWGObserved,run_bind,runWGPrefix_lift,read,write]
    rfl

theorem ReservePoint.selected (point : ReservePoint kid w a h v b middle rest)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    CompleteSelected.Ready ledger debts locals generation pid peer position middle v b := by
  cases point with
  | entry=>exact before
  | reading point=>exact point.selected before
  | read run=>exact (readShape kid).selected before run
  | written read write=>exact (writeShape kid _).selected ((readShape kid).selected before read) write
  | nonce read write=>
    exact selected_append ((writeShape kid _).selected ((readShape kid).selected before read) write) _
      (by intro event member; cases List.mem_singleton.mp member; rfl)
  | reserved read write=>
    rename_i key u c
    have atWrite:=(writeShape kid _).selected ((readShape kid).selected before read) write
    have atNonce:=selected_append atWrite [nonceEvent key]
      (by intro event member; cases List.mem_singleton.mp member; rfl)
    exact selected_append atNonce _ (by intro event member; cases List.mem_singleton.mp member; rfl)

theorem reserve_every_point
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (point : ReservePoint kid w a h v b middle rest) :
    CompleteSelected.Ready ledger debts locals generation pid peer position middle v b ∧
      runWGPrefix (state (Journal.reserve kid)) w a h=runWGPrefix rest v b middle :=
  ⟨point.selected before,point.residual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
