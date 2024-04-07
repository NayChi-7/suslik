package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.{Solution, _}
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.accumulators.SpecSynthesiser.generate_new_spec_with_acc
import org.tygus.suslik.logic.smt.{CyclicProofChecker, SMTSolving}
import org.tygus.suslik.report.{Log, ProofTrace}
import org.tygus.suslik.synthesis.Memoization._
import org.tygus.suslik.synthesis.SearchTree._
import org.tygus.suslik.synthesis.Termination._
import org.tygus.suslik.synthesis.rules.DelegatePureSynthesis
import org.tygus.suslik.synthesis.rules.Rules._
import org.tygus.suslik.synthesis.tactics.Tactic
import org.tygus.suslik.util.SynStats

import scala.Console
import scala.annotation.tailrec

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

class Synthesis(tactic: Tactic, implicit val log: Log, implicit val trace: ProofTrace) extends SepLogicUtils {
  def get_return_type(post_cond: Assertion): String = {
    val sigma = post_cond.sigma
    val sapps = sigma.apps
    val heaplets = sigma.chunks
    var result: String = "type not determined yet"

    val final_payload_ref_opt: Option[Expr] = heaplets.collectFirst {
      case obj: PointsTo => obj.value
    }

    if (final_payload_ref_opt.isEmpty & sapps.length == 1) {
      result = sapps.head.pred
    } else if (final_payload_ref_opt.nonEmpty){
      result = final_payload_ref_opt match {
        case Some(final_payload) =>
          val return_type = sapps.collectFirst {
            case sapp@SApp(pred, List(`final_payload`, _*), _, _) => pred
            case _ =>
              "int"
          }
          return_type.get
      }

    }
    result
  }
  def create_empty_instance(goal: Goal, return_type: String) = {
    var empty_instance: Option[SApp] = None
    var new_args: List[Expr] = List()
    if (return_type == "sll"){
      new_args = List(IntConst(0), SetLiteral(List()))
      empty_instance = Some(SApp("sll", new_args, PTag(0, 0), freshVar(goal.vars, "_pred_")))
    } else if (return_type == "dll") {
      new_args = List(IntConst(0), Var("new_prev_loc"), SetLiteral(List()))
      empty_instance = Some (SApp("dll", new_args, PTag(0, 0), freshVar(goal.vars, "_pred_")))
    } else if (return_type == "lseg") {
      new_args = List(IntConst(0), SetLiteral(List()))
      empty_instance = Some (SApp("lseg", new_args, PTag(0, 0), freshVar(goal.vars, "_pred_")))
    }
    empty_instance
  }
  def synthesizeProc(funGoal: FunSpec, env: Environment, sketch: Statement): (List[Procedure], SynStats) = {
    import log.out.testPrintln
    implicit val config: SynConfig = env.config
    implicit val stats: SynStats = env.stats
    val FunSpec(name, tp, formals, pre, post, var_decl) = funGoal

    if (!CyclicProofChecker.isConfigured()) {
      log.print("Cyclic proof checker is not configured! All termination check will be considered TRUE (this not sound).\n",
        Console.RED, 2)
    } else {
      log.print("The mighty cyclic proof checker is available. Well done!\n",
        Console.GREEN, 2)
    }

    if (config.delegatePure && !DelegatePureSynthesis.isConfigured()) {
      log.print("CVC4 is not available! All pure synthesis steps will be performed by enumeration (this takes more steps).\n",
        Console.RED, 2)
    }

    var goal = topLevelGoal(pre, post, formals, name, env, sketch, var_decl)
    if (config.accumulator) {
      generate_new_spec_with_acc(goal.toFunSpec)
    }
    var safetygoal = goal
    if (goal.env.config.accumulatorHelper) {
      val acc = goal.env.functions.values
      assert(acc.size == 1)
      var (freshSub, f) = acc.head.refreshAll(goal.vars)
      val return_type = get_return_type(f.post)
      val empty_instance = create_empty_instance(goal, return_type)
      assert(empty_instance.nonEmpty)
      val new_sigma = SFormula(goal.pre.sigma.chunks :+ empty_instance.get)
      val new_pre = goal.pre.copy(phi = goal.pre.phi, sigma = new_sigma)
      safetygoal = goal.copy(post = new_pre)
      goal = goal.copy(pre = new_pre)
    }

    log.print("Initial specification:", Console.RESET)
    log.print(s"${goal.pp}\n", Console.BLUE)
    SMTSolving.init()
    memo.clear()
    ProofTrace.current = trace
    try {
      synthesize(goal)(stats = stats) match {
        case Some((body, helpers)) =>
          log.print(s"Succeeded leaves (${successLeaves.length}): ${successLeaves.map(n => s"${n.pp()}").mkString(" ")}", Console.YELLOW, 2)
          synthesize(safetygoal)(stats = stats) match {
            case Some((b,h)) =>
              b match {
                case Skip => testPrintln("Safety goal achieved without any operations")
                case _ => testPrintln("Safety goal error")
              }
            case None => testPrintln("Safety goal error")
          }
          // TODO: check whether the safety goal is achieved without any operations
          val main = Procedure(funGoal, body)
          (main :: helpers, stats)
        case None =>
          log.out.printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp}")
          (Nil, stats)
      }
    } catch {
      case SynTimeOutException(msg) =>
        log.out.printlnErr(msg)
        (Nil, stats)
    }
    
  }

  protected def synthesize(goal: Goal)
                          (stats: SynStats): Option[Solution] = {
    init(goal)
    processWorkList(stats, goal.env.config)
  }

  @tailrec final def processWorkList(implicit
                                     stats: SynStats,
                                     config: SynConfig): Option[Solution] = {
    // Check for timeouts
    if (!config.interactive && stats.timedOut) {
      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut} seconds.\n")
    }

    val sz = worklist.length
    log.print(s"Worklist ($sz): ${worklist.map(n => s"${n.pp()}[${n.cost}]").mkString(" ")}", Console.YELLOW)
    log.print(s"Succeeded leaves (${successLeaves.length}): ${successLeaves.map(n => s"${n.pp()}").mkString(" ")}", Console.YELLOW, 2)
    log.print(s"Memo (${memo.size}) Suspended (${memo.suspendedSize})", Console.YELLOW, 2)
    stats.updateMaxWLSize(sz)

    if (worklist.isEmpty) None // No more goals to try: synthesis failed
    else {
      val (node, addNewNodes) = popNode // Select next node to expand
      val goal = node.goal
      implicit val ctx: log.Context = log.Context(goal)
      stats.addExpandedGoal(node)
      log.print(s"Expand: ${node.pp()}[${node.cost}]", Console.YELLOW) //      <goal: ${node.goal.label.pp}>
      log.print(s"${goal.pp}", Console.BLUE)
      trace.add(node)

      // Lookup the node in the memo
      val res = memo.lookup(goal) match {
        case Some(Failed) => { // Same goal has failed before: record as failed
          log.print("Recalled FAIL", Console.RED)
          trace.add(node, Failed, Some("cache"))
          node.fail
          None
        }
        case Some(Succeeded(sol, id)) =>
        { // Same goal has succeeded before: return the same solution
          log.print(s"Recalled solution ${sol._1.pp}", Console.RED)
          // This seems to always hold in practice because we always get to the companion
          // before we get to any of its children;
          // if this ever fails, we can either:
          // 1. not recall solutions with outgoing backlinks or
          // 2. generate new transitions from these backlinks
          //          assert(sol._1.companions.isEmpty, "Recalled solution with an outgoing backlink, this is unsound!")
          successLeaves = node :: successLeaves // Treat this node as a succeeded leaf
          trace.add(node, Succeeded(sol, id), Some("cache"))
          node.succeed(sol) match {
            case Left(sibling) => {
              worklist = addNewNodes(List(sibling))
              None
            }
            case Right(sol) => Some(sol)
          }
        }
        case Some(Expanded) => { // Same goal has been expanded before: wait until it's fully explored
          log.print("Suspend", Console.RED)
          memo.suspend(node)
          worklist = addNewNodes(List(node))
          None
        }
        case None => expandNode(node, addNewNodes) // First time we see this goal: do expand
      }
      res match {
        case None => processWorkList
        case sol => sol
      }
    }
  }

  // Pop the next node to expand from the worklist;
  // return this node and a strategy for combining its children with the rest of the list
  protected def popNode(implicit config: SynConfig): (OrNode, Worklist => Worklist) =
    if (config.depthFirst) {// DFS? Pick the first one, insert new nodes in the front
      val best = worklist.head
      worklist = worklist.tail
      (best, _ ++ worklist)
    } else if (config.breadthFirst) { // BFS? Pick the first one non-suspended, insert new nodes in the back
      val best = worklist.minBy(n => memo.isSuspended(n))
      val idx = worklist.indexOf(best)
      worklist = worklist.take(idx) ++ worklist.drop(idx + 1)
      (best, worklist ++ _)
    } else { // Otherwise pick a minimum-cost node that is not suspended
      val best = worklist.minBy(n => (memo.isSuspended(n), n.cost))
      val idx = worklist.indexOf(best)
      worklist = worklist.take(idx) ++ worklist.drop(idx + 1)
      (best, worklist.take(idx) ++ _ ++ worklist.drop(idx))
    }

  // Expand node and return either a new worklist or the final solution
  protected def expandNode(node: OrNode, addNewNodes: List[OrNode] => List[OrNode])(implicit stats: SynStats,
                                                                                    config: SynConfig): Option[Solution] = {
    val goal = node.goal
    memo.save(goal, Expanded)
    implicit val ctx = log.Context(goal)

    // Apply all possible rules to the current goal to get a list of alternative expansions,
    // each of which can have multiple open subgoals
    val rules = tactic.nextRules(node)
    val allExpansions = applyRules(rules)(node, stats, config, ctx)
    val expansions = tactic.filterExpansions(allExpansions)

    // Check if any of the expansions is a terminal
    expansions.find(_.subgoals.isEmpty) match {
      case Some(e) =>
        trace.add(e, node)
        successLeaves = node :: successLeaves
        node.succeed(e.producer(Nil)) match {
          case Left(sibling) => {
            // This node had a suspended and-sibling: add to the worklist
            worklist = addNewNodes(List(sibling))
            None
          }
          case Right(sol) => Some(sol) // This node had no more and-siblings: return solution
        }
      case None => { // no terminals: add all expansions to worklist
        // Create new nodes from the expansions
        val newNodes = for {
          (e, i) <- expansions.zipWithIndex
          andNode = AndNode(i +: node.id, node, e)
          if isTerminatingExpansion(andNode) // termination check
          () = trace.add(andNode, andNode.nChildren)
        } yield {
          andNode.nextChild // take the first goal from each new and-node; the first goal always exists
        }

        worklist = addNewNodes(newNodes.toList)
        if (newNodes.isEmpty) {
          // This is a dead-end: prune worklist and try something else
          log.print("Cannot expand goal: BACKTRACK", Console.RED)
          trace.add(node, Failed)
          node.fail
        } else {
          stats.addGeneratedGoals(newNodes.size)
        }
        None
      }
    }
  }


  protected def applyRules(rules: List[SynthesisRule])(implicit node: OrNode,
                                                       stats: SynStats,
                                                       config: SynConfig,
                                                       ctx: log.Context): Seq[RuleResult] = {
    implicit val goal: Goal = node.goal
    rules match {
      case Nil => Vector() // No more rules to apply: done expanding the goal
      case r :: rs =>
        // Invoke the rule
        val children = stats.recordRuleApplication(r.toString, r(goal))

        if (children.isEmpty) {
          // Rule not applicable: try other rules
          applyRules(rs)
        } else {
          // Rule applicable: try all possible sub-derivations
          val childFootprints = children.map(log.showChildren(goal))
          log.print(s"$r (${children.size}): ${childFootprints.head}", Console.RESET)
          for {c <- childFootprints.tail}
            log.print(s" <|>  $c", Console.CYAN)

          if (r.isInstanceOf[InvertibleRule]) {
            // The rule is invertible: do not try other rules on this goal
            children
          } else {
            // Both this and other rules apply
            children ++ applyRules(rs)
          }
        }
    }
  }
}