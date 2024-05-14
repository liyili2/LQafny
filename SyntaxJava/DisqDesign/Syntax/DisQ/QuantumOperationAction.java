package SyntaxJava.DisqDesign.Syntax.DisQ;

public class QuantumOperationAction implements Action {
    private UnitaryExpr operation;
    //private int[] targetQubits; // Array of indices for target qubits
    public int qubitIndex ;
    QuantumValue qv ;
    //public quantumValue qv = new quantumValue ;



    public QuantumOperationAction(UnitaryExpr operation, int qubitIndex , QuantumValue qv) {
        this.operation = operation;
        this.qubitIndex = qubitIndex;
        this.qv=qv;

    }

    public UnitaryExpr getOperation() {
        return operation;
    }

    public int qubitIndex() {
        return qubitIndex;
    }

    public QuantumValue getqv()
    {
        return qv;
    }

    @Override
    public void accept(ActionVisitor visitor) {
        visitor.visit(this);
    }
}

