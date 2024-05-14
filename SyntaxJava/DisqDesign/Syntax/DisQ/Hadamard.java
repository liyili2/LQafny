package SyntaxJava.DisqDesign.Syntax.DisQ;

class Hadamard extends UnitaryExpr {
   // private int[] targetQubits;  // Array to hold the indices of target qubits
    int qubitIndex ;
    QuantumValue quantumValue ;

    public Hadamard(int qubitIndex, QuantumValue quantumValue) {
        this.qubitIndex = qubitIndex;
        this.quantumValue=quantumValue;
    }

    public int getqubitIndex() {
        return qubitIndex;
    }

    public QuantumValue getquantumvalues ()
    {
        return quantumValue ;
    }

    @Override
    public void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
