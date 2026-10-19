import Leanux.Proofs.WG.Progress.NativeSuffixSource
import Leanux.Net.Route

/-! Concrete ambient suffix leaves for routing. IPv4 FIB lookup is intentionally absent: its original nested-loop proof remains a separate obligation. The IPv6 lookup, namespace adapters and actual neighbour classifier are unconditional normal-result contracts. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Proofs.Framing
abbrev NetKeeps (records : List HiddenRecord) {α : Type} (action : Net.M α) : Prop :=
  ∀ s, Preserves (fun a=>Tail records a.hidden) (action.run s)
theorem net_pure {α : Type} (records : List HiddenRecord) (value : α) :
    NetKeeps records (pure value) := fun _=>preserves_pure _

theorem net_bind {α β : Type} (records : List HiddenRecord)
    (action : Net.M α) (next : α→Net.M β)
    (first : NetKeeps records action) (rest : ∀ x,NetKeeps records (next x)) :
    NetKeeps records (action >>= next) := by
  intro s
  rw [StateT.run_bind]
  exact preserves_bind (first s) (fun out=>rest out.1 out.2)

theorem net_get (records : List HiddenRecord) : NetKeeps records (get : Net.M Net.State) :=
  fun _=>preserves_pure _

theorem net_modify (records : List HiddenRecord) (f : Net.State→Net.State) : NetKeeps records (modify f) :=
  fun _=>preserves_pure _

theorem net_ite {α : Type} (records : List HiddenRecord) (p : Prop) [Decidable p]
    (yes no : Net.M α) (hy : NetKeeps records yes) (hn : NetKeeps records no) :
    NetKeeps records (if p then yes else no) := by
  split <;> assumption

theorem net_getTable (records : List HiddenRecord) : NetKeeps records Net.Fib.getTable := by
  unfold Net.Fib.getTable
  exact net_bind records _ _ (net_get records) (fun _=>net_pure records _)
theorem native_liftRouting {α : Type} (records : List HiddenRecord) (action : Net.M α)
    (keep : NetKeeps records action) :
    NativeKeeps records (liftRouting action) := by
  intro g
  unfold liftRouting
  exact preserves_bind (keep _) (fun _=>preserves_pure _)

theorem net_inCreatorNs {α : Type} (records : List HiddenRecord) (action : Net.M α)
    (keep : NetKeeps records action) :
    NetKeeps records (Net.Fib.inCreatorNs action) := by
  unfold Net.Fib.inCreatorNs
  exact net_bind records _ _ (net_get records) (fun _=>
    net_bind records _ _ (net_modify records _) (fun _=>
      net_bind records _ _ keep (fun _=>
        net_bind records _ _ (net_modify records _) (fun _=>net_pure records _))))

theorem net_inSocketNs {α : Type} (records : List HiddenRecord) (action : Net.M α)
    (keep : NetKeeps records action) :
    NetKeeps records (Net.Fib.inSocketNs action) := by
  unfold Net.Fib.inSocketNs
  apply net_bind records _ _ (net_get records)
  intro s
  exact net_ite records _ _ _ (net_inCreatorNs records action keep) keep

theorem net_routeLookup6 (records : List HiddenRecord) (src dst : Nat) :
    NetKeeps records (Net.routeLookup 6 src dst) := by
  change NetKeeps records (do return (←get).toRouting.route6 src dst)
  exact net_bind records _ _ (net_get records) (fun _=>net_pure records _)

theorem net_inetLookupIfaddr (records : List HiddenRecord) (addr : Nat) :
    NetKeeps records (Net.Fib.inetLookupIfaddr addr) := by
  unfold Net.Fib.inetLookupIfaddr
  exact net_ite records _ _ _ (net_pure records _)
    (net_bind records _ _ (net_get records) (fun _=>net_pure records _))

theorem net_neighbourClassify (records : List HiddenRecord) (dev : Nat) :
    NetKeeps records (Net.neighbourClassify dev) := by
  have zero : NetKeeps records (Net.Fib.inetDevAddrType (some dev) 0) := by
    change NetKeeps records (pure Net.Fib.RouteType.broadcast)
    exact net_pure records _
  unfold Net.neighbourClassify
  apply net_bind records _ _ (net_get records)
  intro s
  apply net_ite records _ _ _ (net_pure records _)
  exact net_bind records _ _ zero (fun _=>net_modify records _)
end Leanux.Proofs.WG.Progress.RecordSuffix
