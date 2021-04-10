/**
 * @name Exposure of private information
 * @description If private information is written to an external location, it may be accessible by
 *              unauthorized persons.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id java/exposure-of-private-information
 * @tags security
 *       external/cwe/cwe-359
 */

import java
import semmle.code.java.security.PrivateData
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph

/**
 * A taint-tracking configuration for private information flowing unencrypted to an external location.
 */
class TaintTrackingConfiguration extends TaintTracking::Configuration {
  TaintTrackingConfiguration() { this = "ExposureOfPrivateInformation" }

  override predicate isSource(DataFlow::Node source) { source instanceof PrivateDataSource }

  override predicate isSink(DataFlow::Node sink) { sink instanceof PrivateDataSink }
}

from TaintTrackingConfiguration c, DataFlow::PathNode source, DataFlow::PathNode sink
where c.hasFlowPath(source, sink)
select sink.getNode(), source, sink,
  "Private data returned by $@ is written to an external location.", source.getNode(),
  source.getNode().toString()
