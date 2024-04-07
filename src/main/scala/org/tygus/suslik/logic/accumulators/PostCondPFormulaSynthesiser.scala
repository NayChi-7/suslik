package org.tygus.suslik.logic.accumulators

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic._
import org.tygus.suslik.parsing.SSLParser

object PostCondPFormulaSynthesiser {

  val ACC_LOC = "ans"
  val ACCUMULATOR = "acc"
  val ORIGINAL_LOC = "original_loc"
  val NEW_LOC = "new_loc"
  val FINAL_RESULT = "final_result"

  val ADD_OP_SYMBOLS = List(
    OpOverloadedPlus
  )

  // keep the other conditions the same and all we neeed to handle is including the accumulator to the eq to part
  val LOGIC_OP_RELATED_TO_ACC_P_FORMULA = List(
    OpOverloadedEq
  )

  def get_final_payload(original_post_cond: Assertion) = {
    val sapps = original_post_cond.sigma.apps
    if (sapps.size == 1) {
      sapps.headOption.flatMap(_.args.lift(1))
    } else {
      val heaplets = original_post_cond.sigma.chunks

      val final_payload_ref_opt: Option[Expr] = heaplets.collectFirst {
        case obj: PointsTo => obj.value
      }

      val final_payload = sapps.collectFirst {
        case SApp(_, args, _, _) if args.contains(final_payload_ref_opt.getOrElse("none")) => args.last
      }

      final_payload
    }
  }

  def generate_final_payload_and_acc_combinations(original_post_cond: Assertion) = {
    val final_payload_opt: Option[Expr] = get_final_payload(original_post_cond)
    val payload_list = final_payload_opt.toList :+ Var(ACCUMULATOR)

    val formulas: List[OverloadedBinaryExpr] = for {
      logicOp <- LOGIC_OP_RELATED_TO_ACC_P_FORMULA
      addOp <- ADD_OP_SYMBOLS
      perm <- payload_list.permutations.toList
      if perm.length == 2
    } yield OverloadedBinaryExpr(
      logicOp,
      Var(FINAL_RESULT),
      OverloadedBinaryExpr(
        addOp,
        perm.head,
        perm.last
      )
    )

    val pformulas: List[PFormula] = formulas.map(expr => PFormula(expr))


    val filtered_pformulas_pp = pformulas.map(x => x.pp)

    pformulas
  }


  def extract_p_formula_related_to_final_payload(original_post_cond: Assertion, final_payload_opt: Option[Expr]) = {
    val pformula = original_post_cond.phi

    def helper(expr: Expr): Option[OverloadedBinaryExpr] = expr match {
      case binExpr: OverloadedBinaryExpr if binExpr.overloaded_op == OpOverloadedEq =>
        if (binExpr.left == final_payload_opt.getOrElse(None)) Some(binExpr)
        else helper(binExpr.left).orElse(helper(binExpr.right))
      case _ => None
    }

    pformula.conjuncts.collectFirst {
      case expr: OverloadedBinaryExpr => helper(expr)
    }.flatten

  }


  def add_acc_to_existing_p_formula(concerned_p_formula_opt: Option[OverloadedBinaryExpr]) = {
    val extracted_bin_expr = concerned_p_formula_opt.flatMap {
      case OverloadedBinaryExpr(_, _, binexpr) => Some(binexpr)
      case _ => None
    }

    println(s"extracted bin expr: $extracted_bin_expr")

    val bin_exprs_with_acc_list = ADD_OP_SYMBOLS.map(op => OverloadedBinaryExpr(
      op, extracted_bin_expr.get, Var(ACCUMULATOR)))

    val formulas = bin_exprs_with_acc_list.map(bin_expr => OverloadedBinaryExpr(
      OpOverloadedEq, Var(FINAL_RESULT), bin_expr) )

    val new_p_formulas: List[PFormula] = formulas.map(expr => PFormula(expr))

   new_p_formulas
  }


  def does_p_formula_exist(original_post_cond: Assertion): Boolean = {
    val pformula = original_post_cond.phi
    if (pformula.size == 0) false
    else true
  }

  def generate_new_p_formula(original_post_cond: Assertion) = {
    if (does_p_formula_exist(original_post_cond)) {
      // get the existing p formula and then try to create combinations with payloads from the existing formula and acc
      val final_payload_opt = get_final_payload(original_post_cond)
      val original_p_formula = extract_p_formula_related_to_final_payload(original_post_cond, final_payload_opt)
      println("TESTING")
      println(does_p_formula_exist(original_post_cond))
      add_acc_to_existing_p_formula(original_p_formula)
    }
    else {
      // create combinations of just final payload and acc
      generate_final_payload_and_acc_combinations(original_post_cond)
    }
  }
}
