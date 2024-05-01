package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.function.Function;
class RecursiveProcess implements Process {
    private Function<Process, Process> recursiveDefinition;
    private Process resolvedProcess;

    public RecursiveProcess(Function<Process, Process> recursiveDefinition) {
        this.recursiveDefinition = recursiveDefinition;
        this.resolvedProcess = null;
    }

    public Process getResolvedProcess() {
        if (resolvedProcess == null) {
            resolvedProcess = recursiveDefinition.apply(this);
        }
        return resolvedProcess;
    }

    @Override
    public void accept(ProcessVisitor visitor) {
        visitor.visit(this);
    }
}
