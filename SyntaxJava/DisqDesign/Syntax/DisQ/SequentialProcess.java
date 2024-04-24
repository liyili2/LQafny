import SyntaxJava.DisqDesign.Syntax.DisQ.Action;

class SequentialProcess implements Process {
    private Action action;
    private Process nextProcess;

    public SequentialProcess(Action action, Process nextProcess) {
        this.action = action;
        this.nextProcess = nextProcess;
    }

    public Action getAction() { return action; }
    public Process getNextProcess() { return nextProcess; }

    @Override
    public void accept(ProcessVisitor visitor) {
        visitor.visit(this);
    }
}
