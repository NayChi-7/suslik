package org.tygus.suslik.logic.accumulators

import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic._
import org.tygus.suslik.parsing.SSLParser

object PostCondSFormulaSynthesiser {

  val ACC_LOC = "ans"
  val ACCUMULATOR = "acc"
  val ORIGINAL_LOC = "original_loc"
  val NEW_LOC = "new_loc"
  val FINAL_RESULT = "final_result"
  val NEW_PREV_LOC = "new_prev_loc"

  def get_return_type_and_element(post_cond: Assertion): (String, Option[SApp]) = {
    val sigma = post_cond.sigma
    val sapps = sigma.apps
    val heaplets = sigma.chunks
    var result: (String, Option[SApp]) = ("type not determined yet", None)

    val final_payload_ref_opt: Option[Expr] = heaplets.collectFirst {
      case obj: PointsTo => obj.value
    }

    if (final_payload_ref_opt == None & sapps.length == 1) {
      result = (sapps.head.pred, Some(sapps.head))
    } else {
      result = final_payload_ref_opt match {
        case Some(final_payload) =>
          println(final_payload)
          val return_type_and_element = sapps.collectFirst {
            case sapp@SApp(pred, List(`final_payload`, _*), _, _) => (pred, Some(sapp))
            case sapp@SApp(_, List(_, `final_payload`, _*), _, _) =>
              (determine_return_type_based_on_positionality(sapp), Some(sapp))
          }

          return_type_and_element.get
      }

    }
    result
  }

  def determine_return_type_based_on_positionality(data_structure_associated_with_return_element: SApp) = {
    val data_structure_name = data_structure_associated_with_return_element.pred
    val arguments = data_structure_associated_with_return_element.args
    var return_type = "not determined yet"

    if (data_structure_name == "sll_bounded") {
      return_type = "int"
    } else if (data_structure_name == "treeN") {
      return_type = "int"
    }
    return_type
  }


  def construct_new_return_element(return_payload_obj_and_type: (String, Option[SApp])) = {
    val (return_type, current_return_elem) = return_payload_obj_and_type

    var new_args: List[Expr] = current_return_elem.get.args.toList

    if (return_type == "sll" || return_type == "lseg") {
      new_args = List(Var(NEW_LOC), Var(FINAL_RESULT))
    } else if (return_type == "dll") {
      new_args = List(Var(NEW_LOC), Var(NEW_PREV_LOC), Var(FINAL_RESULT))
    }
    val new_sapp = current_return_elem.get.copy(args = new_args)
    new_sapp
  }


  def construct_new_s_formula(post_cond: Assertion) = {
    val sigma = post_cond.sigma
    val sapps = sigma.apps

    val return_payload_obj_and_type = get_return_type_and_element(post_cond)

    val points_to = {
      if (return_payload_obj_and_type._1 == "int") {
        PointsTo(Var(ACC_LOC), 0, Var(FINAL_RESULT))
      } else {
        PointsTo(Var(ACC_LOC), 0, Var(NEW_LOC))
      }
    }
    val other_elements = sapps.filterNot(x => x == return_payload_obj_and_type._2.get)
    val new_sapp = construct_new_return_element(return_payload_obj_and_type)

    val new_post_cond_sigma = points_to :: new_sapp :: other_elements
    val new_post_cond_sformula = SFormula(new_post_cond_sigma)

    new_post_cond_sformula
  }

}

