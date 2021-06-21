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
private import semmle.javascript.PackageExports as Exports
private import semmle.javascript.security.dataflow.HardcodedCredentialsCustomizations
private import semmle.javascript.security.dataflow.CleartextStorageCustomizations

/** Add properties or variables with a name like "%token%" to the sources of the clear text storage query. */
class TokenSource extends CleartextStorage::Source {
  TokenSource() {
    this.asExpr().(VarAccess).getName().toLowerCase().matches("%token%")
    or
    exists(DataFlow::PropRead pr |
      this = pr and
      pr.getPropertyName().toLowerCase().matches("%token%")
    )
  }

  override string describe() { result = "an access of a token variable" }
}

/** Add logging APIs as sinks to cleartext storage of information. */
class LoggingSink extends CleartextStorage::Sink {
  LoggingSink() {
    exists(CallExpr ce |
      ce.getCalleeName().toLowerCase().regexpMatch("(info|warn|debug|error)") and
      this.asExpr() = ce.getAnArgument()
    )
  }
}

/**
 * A parameter of an exported function, seen as a remote flow source.
 */
class LibraryInputUntrustedDataSource extends RemoteFlowSource, DataFlow::ParameterNode {
  LibraryInputUntrustedDataSource() {
    this = Exports::getALibraryInputParameter() and
    // An AMD-style module sometimes loads the jQuery library in a way which looks like library input.
    not this = JQuery::dollarSource() and
    this.getFile().getRelativePath().regexpMatch("packages/(core|util).*")
  }

  override string getSourceType() { result = "Library input" }

  override predicate isUserControlledObject() { any() }
}

class MockCredentialArgument extends DataFlow::Node {
  MockCredentialArgument() {
    exists(DataFlow::CallNode mockingCall |
      mockingCall = DataFlow::globalVarRef("describe").getACall()
      or
      exists(DataFlow::ModuleImportNode mod |
        mod.getPath() = "nock" and
        mockingCall = mod.getAnInvocation()
      )
    |
      this.asExpr() = mockingCall.getAnArgument().asExpr().getAChild*()
    )
  }
}

class TestCredentialSanitizer extends HardcodedCredentials::Sanitizer {
  TestCredentialSanitizer() {
    (
      this instanceof HardcodedCredentials::Sink
      or
      this instanceof HardcodedCredentials::Source
    ) and
    this.asExpr() = mockCredentialArgument().asExpr().getAChild*()
  }
}

DataFlow::SourceNode mockCredentialArgument(DataFlow::TypeBackTracker t) {
  t.start() and
  result = any(MockCredentialArgument m).getALocalSource()
  or
  exists(DataFlow::TypeBackTracker t2 | result = mockCredentialArgument(t2).backtrack(t2, t))
}

DataFlow::SourceNode mockCredentialArgument() {
  result = mockCredentialArgument(DataFlow::TypeBackTracker::end())
}
