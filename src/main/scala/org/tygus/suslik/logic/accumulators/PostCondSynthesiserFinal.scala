package org.tygus.suslik.logic.accumulators

import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic.accumulators.PostCondPFormulaSynthesiser.generate_new_p_formula
import org.tygus.suslik.logic.accumulators.PostCondSFormulaSynthesiser.construct_new_s_formula

object PostCondSynthesiserFinal {

  def generate_new_post_conds(org_post_cond: Assertion) = {
    val new_p_formulas = generate_new_p_formula(org_post_cond)
    val new_s_formula = construct_new_s_formula(org_post_cond)
    val new_post_conds = new_p_formulas.map(phi =>
      Assertion(phi, new_s_formula))
    new_post_conds
  }

}
