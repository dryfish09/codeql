/**
 * @name Infinite loop with unsatisfiable exit condition
 * @description A loop with an unsatisfiable exit condition could
 *              prevent the program from terminating, making it
 *              vulnerable to a denial of service attack.
 * @kind problem
 * @id cpp/infinite-loop-with-unsatisfiable-exit-condition
 * @problem.severity warning
 * @security-severity 7.5
 * @precision medium
 * @tags security
 *       correctness
 *       external/cwe/cwe-835
 */

import cpp
import semmle.code.cpp.controlflow.BasicBlocks
private import semmle.code.cpp.rangeanalysis.PointlessComparison
import semmle.code.cpp.controlflow.internal.ConstantExprs

/**
 * Holds if there is a control flow edge from `src` to `dst` that
 * can never be taken because `cmp` is provably always `value`.
 */
predicate impossibleEdge(ComparisonOperation cmp, boolean value, BasicBlock src, BasicBlock dst) {
  cmp = src.getEnd() and
  reachablePointlessComparison(cmp, _, _, value, _) and
  if value = true
  then dst = src.getAFalseSuccessor()
  else dst = src.getATrueSuccessor()
}

/**
 * Successor relation with impossible edges removed.
 */
BasicBlock enhancedSucc(BasicBlock bb) {
  result = bb.getASuccessor() and
  not exists(ComparisonOperation cmp, boolean v |
    impossibleEdge(cmp, v, bb, result)
  )
}

/**
 * Holds if `cmp` is provably constant, and that constant value
 * makes the function's exit block unreachable via any path that
 * does not itself cross an impossible edge.
 *
 * Trivial cases such as `while (1) { ... }` do not trigger this,
 * because they have no `ComparisonOperation` condition. We treat
 * those as intentional.
 */
predicate impossibleEdgeCausesNonTermination(ComparisonOperation cmp, boolean value) {
  exists(BasicBlock src, EntryBasicBlock entry |
    impossibleEdge(cmp, value, src, _) and
    // The exit is normally reachable from src...
    src.getASuccessor+() instanceof ExitBasicBlock and
    // ...but not once impossible edges are removed.
    not enhancedSucc+(src) instanceof ExitBasicBlock and
    // And src itself is genuinely reachable from function entry.
    src = enhancedSucc+(entry)
  )
}

from ComparisonOperation cmp, boolean value
where impossibleEdgeCausesNonTermination(cmp, value)
select cmp,
  "Function exit is unreachable because this condition is always " +
    value.toString() + "."
