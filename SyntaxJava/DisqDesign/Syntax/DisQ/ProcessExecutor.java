
class ProcessExecutor implements ProcessVisitor {
    private QuantumState state;

    public ProcessExecutor(QuantumState state) {
        this.state = state;
    }

    @Override
    public void visit(NoOp noOp) {
        // Do nothing
    }

    @Override
    public void visit(SequentialProcess sequentialProcess) {
        sequentialProcess.getAction().perform(state);
        sequentialProcess.getNextProcess().accept(this);
    }

    @Override
    public void visit(ConditionalProcess conditionalProcess) {
        if (conditionalProcess.getCondition().getAsBoolean()) {
            conditionalProcess.getTrueProcess().accept(this);
        } else {
            conditionalProcess.getFalseProcess().accept(this);
        }
    }

    @Override
    public void visit(RecursiveProcess recursiveProcess) {
        recursiveProcess.getResolvedProcess().accept(this);
    }
}
