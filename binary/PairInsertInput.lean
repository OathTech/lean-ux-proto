import PairReplace

namespace Binary.Pair.Insert
open Leanux Leanux.WG

/-- Independent executable decoding of the supplied input tape. Ambient
records are skipped exactly at consumption; later records remain in order.
This is environment data, never a component reconstructed from heap memory. -/
def draw (records : List HiddenRecord) : Except String (Nat × List HiddenRecord) := do
  let records := records.dropWhile fun r => HiddenSite.passive r.site
  let r :: rest := records | throw "insert.input.exhausted"
  unless r.site == HiddenSite.indexDraw.info.id do throw "insert.input.site"
  unless r.bytes.length == 8 && (r.bytes.drop 4).all (· == 0) do
    throw "insert.input.shape"
  let value := (r.bytes.take 4).foldr (fun b acc => acc*256+b.toNat) 0
  return (value,rest)

def record (value : UInt32) : HiddenRecord :=
  ⟨HiddenSite.indexDraw.info.id,
    (List.range 4).map (fun i => UInt8.ofNat (value.toNat / 256^i % 256)) ++ [0,0,0,0]⟩

end Binary.Pair.Insert
