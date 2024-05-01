package SyntaxJava.DisqDesign.Syntax.DisQ;

public interface ProcessVisitor {
    void visit(NoOp noOp);
    void visit(SequentialProcess sequentialProcess);
    void visit(ConditionalProcess conditionalProcess);
    void visit(RecursiveProcess recursiveProcess);
}
