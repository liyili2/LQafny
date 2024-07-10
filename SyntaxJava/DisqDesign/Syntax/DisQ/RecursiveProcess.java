package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.function.Function;

/**
 * Represents a process that has a recursive definition, which can be resolved to an actual process.
 */
class RecursiveProcess implements Process {
    private Function<Process, Process> recursiveDefinition; // Function defining the recursive process
    private Process resolvedProcess; // Cached resolved process

    /**
     * Constructor for initializing a recursive process with its recursive definition.
     * @param recursiveDefinition The function defining the recursive process.
     */
    public RecursiveProcess(Function<Process, Process> recursiveDefinition) {
        this.recursiveDefinition = recursiveDefinition;
        this.resolvedProcess = null; // Initially unresolved
    }

    /**
     * Retrieves the resolved process instance by applying the recursive definition function.
     * If the resolved process has not been computed yet, it computes and caches it.
     * @return The resolved process instance.
     */
    public Process getResolvedProcess() {
        if (resolvedProcess == null) {
            resolvedProcess = recursiveDefinition.apply(this);
        }
        return resolvedProcess;
    }

    /**
     * Accepts a visitor and invokes the appropriate visit method for this recursive process.
     * @param visitor The visitor object visiting this recursive process.
     */
    @Override
    public void accept(ProcessVisitor visitor) {
        visitor.visit(this);
    }
}
