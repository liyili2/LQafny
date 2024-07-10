package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents a no-operation (NoOp) process.
 * Implements the Process interface and allows visitors to visit it.
 */
class NoOp implements Process {

    /**
     * Accepts a visitor and allows it to visit this NoOp process.
     * @param visitor The ProcessVisitor visiting this NoOp process.
     */
    @Override
    public void accept(ProcessVisitor visitor) {
        visitor.visit(this);
    }
}
