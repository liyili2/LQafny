package SyntaxJava.DisqDesign.Syntax.DisQ;

public class QuantumOperationAction implements Action {
    private UnitaryExpr operation;
    private int[] targetQubits; // Array of indices for target qubits

    public QuantumOperationAction(UnitaryExpr operation, int... targetQubits) {
        this.operation = operation;
        this.targetQubits = targetQubits;
    }

    public UnitaryExpr getOperation() {
        return operation;
    }

    public int[] getTargetQubits() {
        return targetQubits;
    }

    @Override
    public void accept(ActionVisitor visitor) {
        visitor.visit(this);
    }
}

