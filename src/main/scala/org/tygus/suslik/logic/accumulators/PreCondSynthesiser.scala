package org.tygus.suslik.logic.accumulators

import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.LocType
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic._
import org.tygus.suslik.parsing.SSLParser

object PreCondSynthesiser {

  val ACC_LOC = "ans"
  val ACCUMULATOR = "acc"
  val ACC_LOC_TYPE = LocType
  val ORIGINAL_LOC = "original_loc"
  val ORIGINAL_PREV_LOC_FOR_DLL = "original_prev_loc"
  val NEW_LOC = "new_loc"

  //TODO: read into the data structure and the positionality to determine the accurate type

  def get_return_type_and_element(post_cond: Assertion): (String, Option[SApp]) = {
    val sigma = post_cond.sigma
    val sapps = sigma.apps
    val heaplets = sigma.chunks
    var result: (String, Option[SApp]) = ("type not determined yet", None)

    val final_payload_ref_opt: Option[Expr] = heaplets.collectFirst {
      case obj: PointsTo => obj.value
    }

    if (final_payload_ref_opt.isEmpty & sapps.length == 1) {
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

  //  PointsTo(Var(z),0,Var(y)), SApp(sll,List(Var(y), Var(acc)),PTag(0,0),Var(_alpha_10)))
  def generate_acc(acc_type: String): Option[SApp] = {
    val new_SApp_option: Option[SApp] =
      if (acc_type == "sll") {
        Some(SApp(acc_type, List(Var(ORIGINAL_LOC), Var(ACCUMULATOR)), PTag(0, 0), Var("_alpha_10")))
      } else if (acc_type == "dll") {
        Some(SApp(acc_type, List(Var(ORIGINAL_LOC), Var(ORIGINAL_PREV_LOC_FOR_DLL), Var(ACCUMULATOR)), PTag(0, 0), Var("_alpha_10")))
      } else if (acc_type == "lseg") {
        Some(SApp(acc_type, List(Var(ORIGINAL_LOC), Var(ACCUMULATOR)), PTag(0, 0), Var("_alpha_10")))
      } else if (acc_type == "int"){
        Some(SApp(acc_type, List(Var(ORIGINAL_LOC), Var(ACCUMULATOR)), PTag(0, 0), Var("_alpha_10")))
      } else {
        println("Data Type is not supported in this version")
        None
      }
    new_SApp_option
  }


  def get_original_SApp(original_pre_cond: Assertion): List[SApp] = {
    val pre_cond_sigma_apps = original_pre_cond.sigma.apps
    pre_cond_sigma_apps
  }

  def generate_new_pre_cond_sigma(original_fun_spec: FunSpec) ={
    val original_pre_cond = original_fun_spec.pre
    val original_post_cond = original_fun_spec.post
    val original_SApp = get_original_SApp(original_pre_cond)
    var new_SApp: List[Heaplet] = original_SApp

    val (acc_type, _) =  get_return_type_and_element(original_post_cond)
    if (acc_type == "int"){
      val points_to = PointsTo(Var(ACC_LOC), 0, Var(ACCUMULATOR))
      new_SApp = points_to :: new_SApp

    } else {
      val points_to = PointsTo(Var(ACC_LOC), 0, Var(ORIGINAL_LOC))
      val acc_SApp = generate_acc(acc_type)

      acc_SApp match {
        case Some(s: SApp) =>
          new_SApp = points_to :: s :: new_SApp

        case None =>
          println("Parsing failed")
          None
      }
    }

    val new_pre_cond = SFormula(new_SApp)
    new_pre_cond
  }


  def generate_new_pre_cond(original_fun_spec: FunSpec): Assertion ={
    val new_pre_cond_phi = original_fun_spec.pre.phi // Keep the original phi
    val new_pre_cond_sigma = generate_new_pre_cond_sigma(original_fun_spec) // Calculate the new sigma
    val new_pre_cond = Assertion(new_pre_cond_phi, new_pre_cond_sigma)
    new_pre_cond
  }
}
