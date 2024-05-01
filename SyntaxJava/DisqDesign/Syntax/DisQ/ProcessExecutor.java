package SyntaxJava.DisqDesign.Syntax.DisQ;

//package SyntaxJava.DisqDesign.Syntax.DisQ;

//import SyntaxJava.DisqDesign.Syntax.DisQ.QuantumState;
//import SyntaxJava.DisqDesign.Syntax.DisQ.ActionVisitor;


public class ProcessExecutor implements ProcessVisitor {
    private QuantumState state;
    private ActionVisitor actionVisitor;

    public ProcessExecutor(QuantumState state) {
        this.state = state;
    }

    @Override
    public void visit(NoOp noOp) {
        // Do nothing
        System.out.println("nothing");
    }

    @Override
    public void visit(SequentialProcess sequentialProcess) {
        sequentialProcess.getAction().accept(actionVisitor);
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
