package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Interface for visiting different types of quantum processes.
 * Each method corresponds to visiting a specific type of process.
 */
public interface ProcessVisitor {
    
    /**
     * Visits a NoOp (no operation) process.
     * @param noOp The NoOp process to visit.
     */
    void visit(NoOp noOp);

    /**
     * Visits a SequentialProcess.
     * @param sequentialProcess The SequentialProcess to visit.
     */
    void visit(SequentialProcess sequentialProcess);

    /**
     * Visits a ConditionalProcess.
     * @param conditionalProcess The ConditionalProcess to visit.
     */
    void visit(ConditionalProcess conditionalProcess);

    /**
     * Visits a RecursiveProcess.
     * @param recursiveProcess The RecursiveProcess to visit.
     */
    void visit(RecursiveProcess recursiveProcess);
}
