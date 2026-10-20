import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadGetterSource

/-! Only the four original staging getter calls select these source trees.
Each tree retains the literal device/slot lookup and its failure branch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

inductive Getter : {α : Type} → Native α → Type where
  | peer (pid : PeerId) : Getter (.peer pid)
  | device : Getter .device
  | key (kid : KeypairId) : Getter (.key kid)
  | owner (kid : KeypairId) : Getter (.owner kid)

def Getter.source : Getter token → ReadGetter.Shape token.action
  | .peer pid => ReadGetter.peer pid
  | .device => ReadGetter.device
  | .key kid => ReadGetter.key kid
  | .owner kid => ReadGetter.owner kid

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
