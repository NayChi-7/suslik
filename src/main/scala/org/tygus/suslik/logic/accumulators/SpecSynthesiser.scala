package org.tygus.suslik.logic.accumulators

import org.tygus.suslik.logic.accumulators.FuncSigSynthesiser.generate_new_func_params
import org.tygus.suslik.logic.accumulators.PostCondSynthesiserFinal.generate_new_post_conds
import org.tygus.suslik.logic.accumulators.PreCondSynthesiser.generate_new_pre_cond
import org.tygus.suslik.logic.{FunSpec, GoalContainer, InductivePredicate}
import org.tygus.suslik.parsing.SSLParser

import java.io.PrintWriter
import java.nio.file.{Files, Paths}


object SpecSynthesiser {

  def generate_new_spec_with_acc(original_spec: FunSpec) = {

    val new_pre_cond = generate_new_pre_cond(original_spec)
    val new_func_params = generate_new_func_params(original_spec)
    val new_post_conds = generate_new_post_conds(original_spec.post)

    val new_specs = new_post_conds.map(x => original_spec.copy(params = new_func_params, pre = new_pre_cond, post = x))
    val new_specs_pp = new_specs.map(x => x.pp)
    new_specs_pp.foreach(println)
    val filePath = "accumulator_specs.txt"
    if (filePath != null && filePath.nonEmpty) {
      try {
        val directoryPath = Paths.get(filePath).getParent
        if (directoryPath != null && !Files.exists(directoryPath)) {
          Files.createDirectories(directoryPath)
        }

        // Using PrintWriter with append mode to write to a file (overwriting existing content)
        val writer = new PrintWriter(Files.newBufferedWriter(Paths.get(filePath)))
        try {
          new_specs_pp.foreach(line => writer.println(line))
        } finally {
          writer.close()
        }
      } catch {
        case e: Exception =>
          println(s"Error writing to file: ${e.getMessage}")
      }
    } else {
      println("File path is not provided.")
    }
  }
}

