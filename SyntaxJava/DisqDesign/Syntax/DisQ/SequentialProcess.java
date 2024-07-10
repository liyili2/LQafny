package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents a sequential process in a quantum program, consisting of an action followed by the next process.
 * Implements Process to signify it's part of the quantum process hierarchy.
 */
class SequentialProcess implements Process {
    private Action action;       // Action to be executed in this sequential process
    private Process nextProcess; // Next process to be executed sequentially

    /**
     * Constructor for initializing a SequentialProcess with an action and the next sequential process.
     * @param action The action to be executed in this sequential process.
     * @param nextProcess The next process to be executed sequentially after the action.
     */
    public SequentialProcess(Action action, Process nextProcess) {
        this.action = action;
        this.nextProcess = nextProcess;
    }

    /**
     * Getter for retrieving the action of this sequential process.
     * @return The action of this sequential process.
     */
    public Action getAction() {
        return action;
    }

    /**
     * Getter for retrieving the next process in sequence after this one.
     * @return The next process in sequence.
     */
    public Process getNextProcess() {
        return nextProcess;
    }

    /**
     * Accepts a visitor and invokes the appropriate visit method for this SequentialProcess.
     * @param visitor The visitor object visiting this SequentialProcess.
     */
    @Override
    public void accept(ProcessVisitor visitor) {
        visitor.visit(this);
    }
}
