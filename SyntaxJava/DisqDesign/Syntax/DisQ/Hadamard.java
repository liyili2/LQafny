package SyntaxJava.DisqDesign.Syntax.DisQ;

class Hadamard extends UnitaryExpr {
    private int[] targetQubits;  // Array to hold the indices of target qubits

    public Hadamard(int... targetQubits) {
        this.targetQubits = targetQubits;
    }

    public int[] getTargetQubits() {
        return targetQubits;
    }

    @Override
    public void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
