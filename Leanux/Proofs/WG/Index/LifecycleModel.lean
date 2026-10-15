import Leanux.Proofs.WG.Index.View

/-! The table invariant permits an absent device. Device initialization and
destruction are boundaries of this invariant, not assertions of owner residency. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

def DeviceTablesSafe (d : Device) : Prop :=
  UniqueIndices d.indexTable ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d

namespace View

/-- Numeric and embedded-owner uniqueness, with the hashed-keypair allocation
bound, for every device that is present in this observation. -/
def TablesSafe (s : Campaign2.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → DeviceTablesSafe d

end View

/-- The device value installed by the original wg_setup. -/
def setupDevice : Device :=
  { ifindex := 0, ifname := "wg0", creatingNet := false, deviceUpdateGen := 0 }

theorem empty_table_safe (d : Device) (empty : d.indexTable = []) : DeviceTablesSafe d := by
  simp [DeviceTablesSafe, UniqueIndices, UniqueOwners, KeypairOwnersBounded, empty]

theorem setupDevice_safe : DeviceTablesSafe setupDevice :=
  empty_table_safe setupDevice rfl

theorem absent_tables_safe (s : Campaign2.Snapshot) (absent : s.wg.device = none) :
    View.TablesSafe s := by
  intro d present
  simp [absent] at present

end Leanux.Proofs.WG.Index
