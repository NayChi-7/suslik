package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language.{CardType, Ident}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.{SApp, _}
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis.Termination.Transition
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.OperationalRules.ReadRule.freshVar
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * Unfolding rules deal with predicates and recursion.
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */

object UnfoldingRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-unfolding"

  object Open extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Open"

    def mkInductiveSubGoals(goal: Goal, h: Heaplet): Option[(Seq[(Expr, Goal)], SApp, SubstVar, Subst)] = {
      val pre = goal.pre
      val env = goal.env

      h match {
        case h@SApp(pred, args, PTag(cls, unf), card) if unf < env.config.maxOpenDepth =>
          ruleAssert(env.predicates.contains(pred), s"Open rule encountered undefined predicate: $pred")
          val freshSuffix = args.take(1).map(_.pp).mkString("_")
          val (InductivePredicate(_, params, clauses), fresh_sbst) = env.predicates(pred).refreshExistentials(goal.vars, freshSuffix)
          // [Cardinality] adjust cardinality of sub-clauses
          val sbst = params.map(_._1).zip(args).toMap + (selfCardVar -> card)
          val remainingSigma = pre.sigma - h
          val newGoals = for {
            c@InductiveClause(_sel, _asn) <- clauses
            sel = _sel.subst(sbst)
            asn = _asn.subst(sbst)
            constraints = asn.phi
            body = asn.sigma
            newPrePhi = pre.phi && constraints && sel
            // The tags in the body should be one more than in the current application:
            _newPreSigma1 = mkSFormula(body.chunks).setSAppTags(PTag(cls, unf + 1))
            newPreSigma = _newPreSigma1 ** remainingSigma
          } yield (sel, goal.spawnChild(Assertion(newPrePhi, newPreSigma),
            childId = Some(clauses.indexOf(c)),
            hasProgressed = true,
            isCompanion = true))

          // This is important, otherwise the rule is unsound and produces programs reading from ghosts
          // We can make the conditional without additional reading
          // TODO: Generalise this in the future
          val noGhosts = newGoals.forall { case (sel, _) => sel.vars.subsetOf(goal.programVars.toSet) }
          if (noGhosts) Some((newGoals, h, fresh_sbst, sbst)) else None
        case _ => None
      }
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      for {
        heaplet <- goal.pre.sigma.chunks
        s <- mkInductiveSubGoals(goal, heaplet) match {
          case None => None
          case Some((selGoals, heaplet, fresh_subst, sbst)) =>
            val (selectors, subGoals) = selGoals.unzip
            val kont = BranchProducer(Some (heaplet), fresh_subst, sbst, selectors) >> ExtractHelper(goal)
            Some(RuleResult(subGoals, kont, this, goal))
        }
      } yield s
    }
  }

  object AbduceCall extends SynthesisRule {

    override def toString: Ident = "TryCall"

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

    // TODO: Generalise this line by analysing the callee's postcondition
    def create_new_args_based_on_post_condition_p_formula (post_cond: Assertion) = {

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


    def apply(goal: Goal): Seq[RuleResult] = {
      val cands = goal.companionCandidates
      val funLabels = cands.map(a => (a.toFunSpec, Some(a.label))) ++ // companions
        goal.env.functions.values.map(f => (f, None)) // components
      for {
        (_f, l) <- funLabels
        (freshSub, f) = _f.refreshAll(goal.vars)

        goal_to_abduce: Goal <- {
          if(1==0){
            val return_type = get_return_type(f.post)
            val empty_instance = create_empty_instance(goal, return_type)

            val new_sigma = if (empty_instance.nonEmpty) {
              SFormula(goal.pre.sigma.chunks :+ empty_instance.get)
            } else {
              goal.pre.sigma
            }

            val new_pre = goal.pre.copy(phi = goal.pre.phi, sigma = new_sigma)
            val new_goal = goal.copy(pre = new_pre)
            Some(new_goal)
          } else {
            Some(goal)
          }
        }

        if multiSubset(f.pre.sigma.profile.apps, goal_to_abduce.pre.sigma.profile.apps)
        if (goal_to_abduce.env.config.maxCalls :: goal_to_abduce.pre.sigma.callTags).min < goal_to_abduce.env.config.maxCalls


        newGamma = goal_to_abduce.gamma ++ (f.params ++ f.var_decl).toMap // Add f's (fresh) variables to gamma
        call = Call(Var(f.name), f.params.map(_._1), l)
        calleePostSigma = f.post.sigma.setSAppTags(PTag(1, 0))
        callePost = Assertion(f.post.phi, calleePostSigma)
        suspendedCallGoal = Some(SuspendedCallGoal(goal_to_abduce.pre, goal_to_abduce.post, callePost, call, freshSub))

        newGoal = goal_to_abduce.spawnChild(post = f.pre, gamma = newGamma, callGoal = suspendedCallGoal)

      } yield {
        val kont: StmtProducer = AbduceCallProducer(f) >> IdProducer >> ExtractHelper(goal_to_abduce)
        RuleResult(List(newGoal), kont, this, goal_to_abduce)
      }
    }
  }

  object CallRule extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Call"

    def apply(goal: Goal): Seq[RuleResult] = {
      if (goal.callGoal.isEmpty) return Nil // this goal has no suspended call

      val pre = goal.pre
      val post = goal.post
      val callGoal = goal.callGoal.get.applySubstitution
      val call = callGoal.call
      // In case of a non-recursive call, there might be no predicates in the callee post, and hence no call tags:
      val callTag = (0 :: (callGoal.callerPre.sigma - goal.pre.sigma).callTags).max + 1
      val noGhostArgs = call.args.forall(_.vars.subsetOf(goal.programVars.toSet))

      if (post.sigma.isEmp &&                                   // companion's transformed pre-heap is empty
        goal.existentials.isEmpty &&                            // no existentials
        callTag <= goal.env.config.maxCalls &&
        noGhostArgs &&                                          // TODO: if slow, move this check to when substitution is made
        SMTSolving.valid(pre.phi ==> post.phi))                 // pre implies post
      {
        val calleePostSigma = callGoal.calleePost.sigma.setSAppTags(PTag(callTag))
        val newPre = Assertion(pre.phi && callGoal.calleePost.phi, pre.sigma ** calleePostSigma)
        val newPost = callGoal.callerPost
        val newGoal = goal.spawnChild(pre = newPre, post = newPost, callGoal = None, isCompanion = true)
        val postCallTransition = Transition(goal, newGoal)
        val kont: StmtProducer = SubstMapProducer(callGoal.freshToActual) >> PrependProducer(call) >> ExtractHelper(goal)
        List(RuleResult(List(newGoal), kont, this,
          List(postCallTransition) ++ companionTransition(callGoal, goal)))
      }
      else Nil
    }

    def companionTransition(callGoal: SuspendedCallGoal, goal: Goal): Option[Transition] = callGoal.call.companion match {
      case None => None // Non-recursive call does not correspond to transition in the trace
      case Some(label) => {
        val companion = goal.ancestorWithLabel(label).get
        val cardVars = companion.pre.vars.filter(_.getType(companion.gamma).contains(CardType)).toList
        val sub = compose(callGoal.companionToFresh, callGoal.freshToActual)
        val nonProgressingFlipped = cardVars.zip(cardVars.map(_.subst(sub))).filter(_._2.isInstanceOf[Var])
        val nonProgressing = nonProgressingFlipped.map{ case (v, e) => (e.asInstanceOf[Var], v) }
        Some(Transition(goal.label, label, List(), nonProgressing))
      }
    }
  }



  /*
  Close rule: unroll a predicate in the post-state

              p(params) := { true ? b }
    Γ ; { φ ; P } ; { ψ ; b[args/params] * Q } ---> S
    ---------------------------------------------------- [close]
        Γ ; { φ ; P } ; { ψ ; p(args) * Q } ---> S

   */
  object Close extends SynthesisRule {

    override def toString: Ident = "Close"

    def apply(goal: Goal): Seq[RuleResult] = {
      val post = goal.post
      val env = goal.env

      def heapletResults(h: Heaplet): Seq[RuleResult] = h match {
        case a@SApp(pred, args, PTag(cls, unf), card) =>
          if (unf >= env.config.maxCloseDepth) return Nil

          ruleAssert(env.predicates.contains(pred),
            s"Close rule encountered undefined predicate: $pred")
          val (InductivePredicate(predName, params, clauses), predSbst) = env.predicates(pred).refreshExistentials(goal.vars)

          //ruleAssert(clauses.lengthCompare(1) == 0, s"Predicates with multiple clauses not supported yet: $pred")
          val paramNames = params.map(_._1)

          // [Cardinality] adjust cardinality of sub-clauses
          val substArgs = paramNames.zip(args).toMap + (selfCardVar -> card)

          val subDerivations = for {
            InductiveClause(selector, asn) <- clauses
            // Make sure that existential in the body are fresh
            asnExistentials = asn.vars -- paramNames.toSet -- Set(selfCardVar)
            freshSuffix = args.take(1).map(_.pp).mkString("_")
            freshExistentialsSubst = refreshVars(asnExistentials.toList, goal.vars, freshSuffix)
            // Make sure that can unfold only once
            actualAssertion = asn.subst(freshExistentialsSubst).subst(substArgs)
            actualConstraints = actualAssertion.phi
            actualBody = actualAssertion.sigma.setSAppTags(PTag(cls, unf + 1))
            // If we unfolded too much: back out
            //             if !actualBody.chunks.exists(h => exceedsMaxDepth(h))
          } yield {
            val actualSelector = selector.subst(freshExistentialsSubst).subst(substArgs)
            val newPhi = post.phi && actualConstraints && actualSelector
            val newPost = Assertion(newPhi, goal.post.sigma ** actualBody - h)

            val kont = UnfoldProducer(a, selector, Assertion(actualConstraints, actualBody), predSbst ++ freshExistentialsSubst) >> IdProducer >> ExtractHelper(goal)

            RuleResult(List(goal.spawnChild(post = newPost)), kont, this, goal)
          }
          subDerivations
        case _ => Nil
      }

      for {
        h <- goal.post.sigma.chunks
        s <- heapletResults(h)
      } yield s
    }
  }
}
