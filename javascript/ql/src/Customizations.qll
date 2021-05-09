/**
 * Contains customizations to the standard library.
 *
 * This module is imported by `javascript.qll`, so any customizations defined here automatically
 * apply to all queries.
 *
 * Typical examples of customizations include adding new subclasses of abstract classes such as
 * `FileSystemAccess`, or the `Source` and `Sink` classes associated with the security queries
 * to model frameworks that are not covered by the standard library.
 */

import javascript
import semmle.javascript.heuristics.AdditionalSources

/**
 * A `RESTDataSource` as defined for an Apollo server.
 */
class RESTDataSource extends ClassDefinition {
  RESTDataSource() {
    exists(DataFlow::SourceNode sup | sup.flowsToExpr(getSuperClass()) |
      sup = DataFlow::moduleMember("apollo-datasource-rest", "RESTDataSource")
    )
  }

  /** Gets a reference to an instance of this component. */
  pragma[noinline]
  DataFlow::SourceNode getAnInstanceReference() {
    result.analyze().getAValue() = AbstractInstance::of(this)
    or
    result = any(ApolloServer apolloServer).getADataSourceUse(this)
  }

  /** Gets a call to the named method. */
  DataFlow::CallNode getACall(string methodName) {
    result.getReceiver() = getAnInstanceReference().getALocalUse() and
    result.getCalleeName() = methodName
  }
}

/** A client REST API request via Apollo. */
class ApolloRestRequest extends ClientRequest::Range, DataFlow::CallNode {
  ApolloRestRequest() {
    // Taken from https://github.com/apollographql/apollo-server/blob/main/packages/apollo-datasource-rest/src/RESTDataSource.ts#L154-L202
    this = any(RESTDataSource rds).getACall(["get", "post", "patch", "put", "delete"])
  }

  override DataFlow::Node getUrl() { result = getArgument(0) }

  override DataFlow::Node getHost() { none() } // TODO could look for this.baseURL

  override DataFlow::Node getAResponseDataNode(string responseType, boolean promise) {
    responseType = "json" and
    promise = true and
    result = this
  }

  override DataFlow::Node getADataNode() { result = getArgument(1) }

  override DataFlow::Node getASavePath() {
    exists(DataFlow::CallNode write |
      write = DataFlow::moduleMember("fs", "createWriteStream").getACall() and
      write = this.getAMemberCall("pipe").getArgument(0).getALocalSource() and
      result = write.getArgument(0)
    )
  }
}

/** Data returned by a REST response */
class ApolloRestResponse extends HeuristicSource, RemoteFlowSource, DataFlow::CallNode {
  ApolloRestResponse() { exists(ApolloRestRequest r | this = r.getAResponseDataNode(_, _)) }

  override string getSourceType() {
    result = "a REST response from an Apollo datasource call to a remote server"
  }
}

class ApolloServer extends DataFlow::NewNode {
  ApolloServer() {
    this = DataFlow::moduleImport("apollo-server").getAConstructorInvocation("ApolloServer")
  }

  /** Gets a `DataFlow::FunctionNode` which initializes the `dataSources` array. */
  DataFlow::FunctionNode getADataSourcesInit() {
    result = getOptionArgument(0, "dataSources").getABoundFunctionValue(0)
  }

  /** Get a RESTDataSource specified during this server construction. */
  RESTDataSource getARestDataSource(string propName) {
    exists(DataFlow::SourceNode ln |
      ln.getALocalUse() = getADataSourcesInit().getAReturn() and
      ln.hasPropertyWrite(propName, result.getAnInstanceReference())
    )
  }

  DataFlow::SourceNode getResolvers() { result.getALocalUse() = getOptionArgument(0, "resolvers") }

  DataFlow::SourceNode getResolverQuery() {
    getResolvers().hasPropertyWrite("Query", result.getALocalUse())
  }

  DataFlow::FunctionNode getAQuery() { getResolverQuery().hasPropertyWrite(_, result) }

  DataFlow::SourceNode getDataSourcesParameter() {
    result = getAQuery().getParameter(2).getAPropertyRead("dataSources")
  }

  DataFlow::PropRead getADataSourceUse(RESTDataSource rds) {
    rds = getARestDataSource(result.getPropertyName()) and
    result.getBase() = getDataSourcesParameter().getALocalUse()
  }
}

/** A `SharedTaintStep` for tracking flow from the datasources to resolvers in `ApolloServer`s. */
class ApolloDataSourcesTaintStep extends TaintTracking::SharedTaintStep {
  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists(DataFlow::CallNode c, DataFlow::FunctionNode mn, RESTDataSource rds, string methodName |
      c = rds.getACall(methodName) and
      mn.getFunction() = rds.getMethod(methodName).getBody() and
      pred = mn.getAReturn() and
      succ = c
    )
  }
}