import Leanux.Proofs.WG.Config.AllowedOrderInspectionBridge

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.AllowedOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise
open Leanux.Proofs.Framing Lifetimes Std.Do

theorem inspection_outcome (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (w : WGWorld) (ambient : Ambient) :
    (inspection attrs peer flags psk pid w ambient).outcome =
      Campaign2.observeResult (((peerConfigUpdateSource attrs peer flags psk pid).run w).run ambient) := by
  exact congrArg Campaign2.observeResult (peerConfigUpdateObserved_erases attrs peer flags psk pid w ambient [])

theorem inspection_facts (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (w : WGWorld) (ambient : Ambient) :
    Facts attrs peer flags psk pid (Campaign2.snapshot w ambient)
      (inspection attrs peer flags psk pid w ambient) := by
  obtain ⟨suffix,eq,safe,post⟩:=update_spec attrs peer flags psk pid [] w ambient [] rfl
  obtain ⟨events,history,path⟩:=safe
  have known : (inspection attrs peer flags psk pid w ambient).completions=events := by
    simpa only [inspection,runWGPrefix,runStatePrefix,List.nil_append] using history
  refine ⟨⟨w,ambient,rfl,rfl⟩,by simpa only [known] using path,?_⟩
  cases outcome : (runPrefix (StateT.run (peerConfigUpdateObserved attrs peer flags psk pid) w) ambient []).1 with
  | error stop=>
    simp only [inspection,runWGPrefix,runStatePrefix,Campaign2.observeResult,outcome,Except.map]
  | ok value=>
    obtain ⟨⟨ret,v⟩,after⟩:=value
    simp only [outcome] at post
    obtain ⟨events,history,finished⟩:=post
    have same : (inspection attrs peer flags psk pid w ambient).completions=events := by
      simpa only [inspection,runWGPrefix,runStatePrefix,List.nil_append] using history
    simpa only [inspection,runWGPrefix,runStatePrefix,Campaign2.observeResult,outcome,Except.map] using
      (show UpdateFinished attrs peer flags pid (inspection attrs peer flags psk pid w ambient).completions ret by
        simpa only [same] using finished)

theorem inspection_routed (tables : FlatTable×FlatTable) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (w : WGWorld) (ambient : Ambient)
    (target : RoutedTarget tables pid (Campaign2.snapshot w ambient)) :
    RoutedFacts tables (inspection attrs peer flags psk pid w ambient) := by
  have start : CompletionTarget tables pid [] w := ⟨⟨.nil,target.1⟩,target.2⟩
  obtain ⟨suffix,eq,safe,post⟩:=
    peerConfigUpdateObserved_spec tables attrs shape peer flags psk pid w ambient [] start
  refine ⟨safe,?_⟩
  cases outcome : (runPrefix (StateT.run (peerConfigUpdateObserved attrs peer flags psk pid) w) ambient []).1 with
  | error stop=>
    simp only [inspection,runWGPrefix,runStatePrefix,Campaign2.observeResult,outcome,Except.map]
  | ok value=>
    obtain ⟨⟨ret,v⟩,after⟩:=value
    simp only [outcome] at post
    simp only [inspection,runWGPrefix,runStatePrefix,Campaign2.observeResult,outcome,Except.map]
    exact post.2

end Leanux.Proofs.WG.Config.AllowedOrder
