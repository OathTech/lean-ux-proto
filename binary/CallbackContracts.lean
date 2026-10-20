import CallbackAgreement
import CallbackPc
import CallbackWrappers

namespace Binary.Callback
open TrustBase

theorem bh_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    BhEnableContract fetch := service_agreement agree bh_image_contract

theorem pc_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    TracePcContract fetch := service_agreement agree pc_image_contract

theorem cmp4_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    TraceCmp4Contract fetch := service_agreement agree cmp4_image_contract

theorem const_cmp4_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    TraceConstCmp4Contract fetch := service_agreement agree const_cmp4_image_contract

theorem const_cmp1_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    TraceConstCmp1Contract fetch := service_agreement agree const_cmp1_image_contract

#print axioms cmp4_contract
#print axioms const_cmp4_contract
#print axioms const_cmp1_contract
#print axioms bh_contract
#print axioms pc_contract
end Binary.Callback
