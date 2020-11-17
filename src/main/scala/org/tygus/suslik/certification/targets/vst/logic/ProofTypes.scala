package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.clang.CTypes.VSTCType
import org.tygus.suslik.certification.targets.vst.clang.{CTypes, PrettyPrinting}


/** Encapsulates all types used in proofs - i.e if these types are pretty printed, then they will be valid Coq terms */
object ProofTypes {

  def proof_type_of_c_type(vst: VSTCType) : VSTProofType =
    vst match {
      case CTypes.CIntType => CoqParamType(vst)
      case CTypes.CVoidPtrType => CoqParamType(vst)
      case CTypes.CUnitType => ???
    }

  /** proof types */
  sealed abstract class VSTProofType extends PrettyPrinting {

    /** prints the type as a term of type type (VST's definition) in Coq  */
    def pp_as_ctype: String =
      this match {
        case CoqParamType(ty) => ty match {
          case CTypes.CIntType => "tint"
          case CTypes.CVoidPtrType => "(tptr (Tunion _sslval noattr))"
        }
        case CoqPtrType => "(tptr tvoid)"
        case CoqIntType => "tint"
        case CoqListType(elem, length) => s"(tarray ${elem.pp_as_ctype} ${length.get})"
      }
  }

  /** represents a val type in vst that maps to a parameter to the function of type ty */
  case class CoqParamType(ty: VSTCType) extends VSTProofType {
    override def pp : String = "val"
  }

  case object CoqPtrType extends VSTProofType {
    override def pp: String = "val"
  }

  case object CoqBoolType extends VSTProofType {
    override def pp: String = ???
  }

  /** type of integers (used to represent the values of variables in a C program) */
  case object CoqIntType extends VSTProofType {
    override def pp:String = "Z"
  }

  /** type of natural numbers (used to type metavariables in Coq proofs) */
  case class CoqCardType(pred_type: String) extends VSTProofType {
    override def pp:String = s"${pred_type}_card"
  }

  sealed case class CoqListType(elem: VSTProofType, length: Option[Int]) extends VSTProofType {
    override def pp: String = s"(list ${elem.pp})"
  }


}
