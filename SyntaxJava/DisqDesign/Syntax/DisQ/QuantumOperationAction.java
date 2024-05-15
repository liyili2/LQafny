package SyntaxJava.DisqDesign.Syntax.DisQ;

public class QuantumOperationAction implements Action {
    private UnitaryExpr operation;
    //private int[] targetQubits; // Array of indices for target qubits
    public int qubitIndex , control , target;
    double theta;
    //QuantumValue qv ;
    //public quantumValue qv = new quantumValue ;



    public QuantumOperationAction(UnitaryExpr operation, int qubitIndex) {
        this.operation = operation;
        this.qubitIndex = qubitIndex;
        //this.qv=qv;

    }

    public QuantumOperationAction (UnitaryExpr operation, int qubitIndex, double theta)
    {
        this.operation = operation;
        this.qubitIndex = qubitIndex;
        this.theta=theta;
    }

    public QuantumOperationAction(UnitaryExpr operation, int control, int target)
    {
        this.operation = operation;
        this.control = control;
        this.target=target;
    }

    public UnitaryExpr getOperation() {
        return operation;
    }

    public int qubitIndex() {
        return qubitIndex;
    }

   /**  public QuantumValue getqv()
    {
        return qv;
    } **/

    @Override
    public void accept(ActionVisitor visitor) {
        visitor.visit(this);
    }
}

