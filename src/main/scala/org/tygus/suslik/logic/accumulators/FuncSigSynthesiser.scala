package org.tygus.suslik.logic.accumulators

import org.tygus.suslik.language.Expressions.{IntConst, Var}
import org.tygus.suslik.language.{LocType, SSLType}
import org.tygus.suslik.logic.{FunSpec, GoalContainer, InductivePredicate, PointsTo}
import org.tygus.suslik.parsing.SSLParser

object FuncSigSynthesiser {

  val LOC_ACC = "ans"
  val LOC_ACC_TYPE = LocType

  val LOC_PARAM = (Var(LOC_ACC), LOC_ACC_TYPE)

  def generate_new_func_params(original_func_spec: FunSpec): List[(Var, SSLType)] ={
    val original_params = original_func_spec.params
    val heaplets = original_func_spec.pre.sigma.chunks
    val points_to_heaplet = heaplets.collectFirst {
      case obj: PointsTo => (obj.loc, obj.value)
    }
    var new_params = original_params

    points_to_heaplet match {
      case Some((points_to_loc, points_to_address)) =>
        val new_points_to_heaplet_loc =  if (points_to_address.equals(IntConst(0))){
          (points_to_loc.vars.head, LocType)
        } else {
          (points_to_address.vars.head, LocType)
        }

        new_params = LOC_PARAM :: new_points_to_heaplet_loc ::
          original_params.filterNot(x => x._1 == points_to_loc)
      case None =>
        new_params = LOC_PARAM :: original_params
    }
    new_params
  }
}


