import Leanux.Proofs.WG.Config.WeightedGetterModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Equal serialized prefix sizes preserve the actual weighted boundary
domain and DATA/DONE receive count. The node serializer and costs are held
fixed, while endpoint values and all other device/peer fields may differ. -/
theorem weightedPagination_spaces (d e : Device) (p q : Peer)
    (deviceSpace : devicePrefixSpace d = devicePrefixSpace e)
    (peerSpace : peerFixedSpace p = peerFixedSpace q)
    (nodes : NodeId → AipNode) (ids : List NodeId) :
    (weightedGetterFresh d p nodes ids ↔ weightedGetterFresh e q nodes ids) ∧
      weightedGetterReceives d p nodes ids = weightedGetterReceives e q nodes ids := by
  have tail : ∀ pages, weightedTailReceives d nodes pages = weightedTailReceives e nodes pages := by
    intro pages
    induction pages with
    | nil => rfl
    | cons page rest ih => simp only [weightedTailReceives,deviceSpace,ih]
  have first : (mixedFirstCall d p nodes ids).skb.room = (mixedFirstCall e q nodes ids).skb.room := by
    cases ids <;> simp [mixedFirstCall,socketCallbackResult,deviceSpace,peerSpace]
  constructor
  · simp only [weightedGetterFresh,deviceSpace,peerSpace]
  · simp only [weightedGetterReceives,deviceSpace,peerSpace,first,tail]

end Leanux.Proofs.WG.Config
