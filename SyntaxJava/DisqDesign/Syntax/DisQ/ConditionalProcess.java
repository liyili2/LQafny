package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.function.BooleanSupplier;

/**
 * Represents a conditional process that selects between two processes based on a boolean condition.
 * This class allows conditional execution of different processes within a quantum computing or distributed systems context.
 */
class ConditionalProcess implements Process {
    private BooleanSupplier condition; // The condition that determines which process to execute.
    private Process trueProcess;       // The process to execute if the condition is true.
    private Process falseProcess;      // The process to execute if the condition is false.

    /**
     * Constructs a ConditionalProcess with a condition and two processes.
     * @param condition The boolean supplier that provides the condition to choose between processes.
     * @param trueProcess The process to execute if the condition is true.
     * @param falseProcess The process to execute if the condition is false.
     */
    public ConditionalProcess(BooleanSupplier condition, Process trueProcess, Process falseProcess) {
        this.condition = condition;
        this.trueProcess = trueProcess;
        this.falseProcess = falseProcess;
    }

    /**
     * Gets the boolean supplier that provides the condition for this conditional process.
     * @return The boolean supplier defining the condition.
     */
    public BooleanSupplier getCondition() {
        return condition;
    }

    /**
     * Gets the process to execute if the condition is true.
     * @return The process to execute when the condition is true.
     */
    public Process getTrueProcess() {
        return trueProcess;
    }

    /**
     * Gets the process to execute if the condition is false.
     * @return The process to execute when the condition is false.
     */
    public Process getFalseProcess() {
        return falseProcess;
    }

    /**
     * Accepts a visitor that implements the ProcessVisitor interface.
     * This method allows the visitor to process this conditional process,
     * enabling operations on conditional processes without changing their classes.
     * @param visitor The visitor that will process this conditional process.
     */
    @Override
    public void accept(ProcessVisitor visitor) {
        visitor.visit(this); // Delegate the processing of this conditional process to the visitor.
    }
}
