package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.synthesis.instances.SimpleSynthesis

/**
  * @author Ilya Sergey
  */

class AccountTests extends FunSpec with Matchers with SynthesisTestUtil {

  val synthesis: Synthesis = new SimpleSynthesis

  def doTest(desc: String, in: String, out: String): Unit =
    it(desc) {
      synthesizeFromSpec(in, out)
    }

  describe("SL-based synthesizer with one-constructor predicates") {
    runAllTestsFromDir("account")
  }

}