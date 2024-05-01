package SyntaxJava.DisqDesign.Syntax.DisQ;

class NoOp implements Process {
    @Override
    public void accept(ProcessVisitor visitor) {
        visitor.visit(this);
    }
}