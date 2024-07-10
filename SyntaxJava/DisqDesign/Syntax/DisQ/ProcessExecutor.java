package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Executor for quantum processes defined by various Process implementations.
 * This executor interprets and executes quantum processes using a visitor pattern.
 */
public class ProcessExecutor implements ProcessVisitor {
    
    private QuantumState1 state2;   // Quantum state to apply actions on
    private ActionVisitor actionVisitor;  // Visitor for interpreting actions within processes

    /**
     * Constructor to initialize the ProcessExecutor with a quantum state.
     * @param state2 The quantum state to operate actions on.
     */
    public ProcessExecutor(QuantumState1 state2) {
        this.state2 = state2;
        this.actionVisitor = new ActionInterpreter(state2);  // Initialize the action interpreter
    }

    /**
     * Implements the visit method for a NoOp (no operation) process.
     * Performs no action and prints a message indicating no operation was performed.
     * @param noOp The NoOp object to visit.
     */
    @Override
    public void visit(NoOp noOp) {
        // Do nothing
        System.out.println("No operation performed");
    }

    /**
     * Implements the visit method for a SequentialProcess.
     * Executes the action associated with the sequential process and then visits the next process.
     * @param sequentialProcess The SequentialProcess object to visit.
     */
    @Override
    public void visit(SequentialProcess sequentialProcess) {
        sequentialProcess.getAction().accept(actionVisitor);  // Execute the action of the sequential process
        sequentialProcess.getNextProcess().accept(this);  // Visit the next process in sequence
    }

    /**
     * Implements the visit method for a ConditionalProcess.
     * Evaluates the condition and executes the true or false process accordingly.
     * @param conditionalProcess The ConditionalProcess object to visit.
     */
    @Override
    public void visit(ConditionalProcess conditionalProcess) {
        if (conditionalProcess.getCondition().getAsBoolean()) {
            conditionalProcess.getTrueProcess().accept(this);  // Execute the true process if condition is true
        } else {
            conditionalProcess.getFalseProcess().accept(this);  // Execute the false process if condition is false
        }
    }

    /**
     * Implements the visit method for a RecursiveProcess.
     * Executes the resolved process recursively.
     * @param recursiveProcess The RecursiveProcess object to visit.
     */
    @Override
    public void visit(RecursiveProcess recursiveProcess) {
        recursiveProcess.getResolvedProcess().accept(this);  // Execute the resolved process recursively
    }
}
