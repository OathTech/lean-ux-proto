import Leanux.Runner
import Leanux.Proofs.Framing.Tools

/-! Bounds follow from the actual list of UInt8 values. No assumption about
hex decoding or a requested address width enters these arithmetic lemmas. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Lean

/-- The source fold, also useful for packet-header slices. -/
def addressValue (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem addressFold_bound (bytes : List UInt8) (acc : Nat) :
    bytes.foldl (fun acc b => acc * 256 + b.toNat) acc < (acc + 1) * 256 ^ bytes.length := by
  induction bytes generalizing acc with
  | nil => simp
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    have hh := ih (acc * 256 + b.toNat)
    have hp : 0 < 256 ^ bs.length := Nat.pow_pos (by decide)
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ] at *
    calc
      _ < (acc * 256 + b.toNat + 1) * 256 ^ bs.length := hh
      _ ≤ ((acc + 1) * 256) * 256 ^ bs.length := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ac_rfl

theorem addressValue_bound (bytes : List UInt8) : addressValue bytes < 256 ^ bytes.length := by
  simpa only [addressValue, Nat.zero_add, Nat.one_mul] using addressFold_bound bytes 0

/-- An address, when present, fits its actual byte length. Absence remains
absence; family validity and CIDR validity are separate source guards. -/
def AddressShape (ip : WG.AllowedIpAttrs) : Prop :=
  ∀ addr, ip.addr = some addr → addr < 256 ^ ip.addrLen

def EntryAddressShape : WG.AllowedIpEntry → Prop
  | .malformed => True
  | .attrs ip => AddressShape ip

theorem addressShape_bytes (family cidr : Option Nat) (bytes : Option (List UInt8)) :
    AddressShape { family := family, addr := bytes.map addressValue, addrLen := (bytes.map List.length).getD 0, cidr := cidr } := by
  cases bytes with
  | none => simp [AddressShape]
  | some bs =>
    intro addr ha
    cases ha
    exact addressValue_bound bs

/-- Pinned reference to the original private parser, not a replacement parser. -/
def parseAllowedIp := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.parseAllowedIp

macro "parser_unfold " n:ident : tactic =>
  `(tactic| unfold $(Lean.mkCIdent (Leanux.Proofs.Framing.normalizePinnedName n.getId)) at *)

theorem parseAllowedIp_shape (j : Json) (what : String) (entry : WG.AllowedIpEntry)
    (hr : parseAllowedIp j what = .ok entry) : EntryAddressShape entry := by
  unfold parseAllowedIp at hr
  parser_unfold _private.Leanux.Runner.«0».Leanux.Runner.parseAllowedIp
  simp only [bind, Except.bind, pure, Except.pure] at hr
  repeat' first | split at hr | contradiction
  all_goals try (cases hr; trivial)
  all_goals cases hr
  all_goals apply addressShape_bytes

end Leanux.Proofs.WG.AllowedIps
