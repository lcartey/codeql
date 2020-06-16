/**
 * @name Untrusted data passed to external API
 * @description Data provided remotely is used in this external API.
 * @id java/terminating-use-of-tainted-data
 * @kind path-problem
 * @precision low
 * @severity warning
 */

import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph

/** A method which is uninteresting to report */
class UninterestingMethod extends Method {
  UninterestingMethod() {
    this instanceof EqualsMethod
    or
    this.getDeclaringType().hasQualifiedName("org.apache.commons.lang3", "Validate")
    or
    getQualifiedName() = "Objects.equals"
    or
    getDeclaringType().hasQualifiedName("com.google.common.base", "Preconditions")
    or
    getDeclaringType().getPackage().getName().matches("org.junit%")
    or
    getDeclaringType().hasQualifiedName("com.google.common.base", "Strings") and
    getName() = "isNullOrEmpty"
  }
}

/** A node which has no outgoing taint steps. */
class TerminalNode extends DataFlow::Node {
  Call call;
  TerminalNode() {
    // Argument to call to method defined outside this database
    this.asExpr() = call.getAnArgument() and
    not exists(call.getCallee().getBody()) and
    // Not already modelled as a taint step
    not exists(DataFlow::Node next |
      TaintTracking::localTaintStep(this, next)
    ) and
    // Not a call to an uninteresting method
    not call.getCallee() instanceof UninterestingMethod and
    // Not a call to an method which is overridden
    not exists(Method m |
      m.getASourceOverriddenMethod() = call.getCallee().getSourceDeclaration()
    )
  }

  /** Gets the `Method` being called by this terminal node. */
  Method getMethod() {
    result = call.getCallee()
  }
}

class TerminalConfig extends TaintTracking::Configuration {
  TerminalConfig() { this = "TerminalConfig" }

  override predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  override predicate isSink(DataFlow::Node sink) { sink instanceof TerminalNode }
}

from TerminalConfig config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink, source, sink, "Call to " + sink.getNode().(TerminalNode).getMethod().getQualifiedName() + " with untrusted data from $@.", source, source.toString()