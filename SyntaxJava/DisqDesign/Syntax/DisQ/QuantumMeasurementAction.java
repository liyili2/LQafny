package SyntaxJava.DisqDesign.Syntax.DisQ;

public class QuantumMeasurementAction implements Action {
    private int[] targetQubits; // Indices of qubits to be measured
    private String resultVariable; // Variable to store measurement results

    public QuantumMeasurementAction(int[] targetQubits, String resultVariable) {
        this.targetQubits = targetQubits;
        this.resultVariable = resultVariable;
    }

    public int[] getTargetQubits() {
        return targetQubits;
    }

    public String getResultVariable() {
        return resultVariable;
    }

    @Override
    public void accept(ActionVisitor visitor) {
        visitor.visit(this);
    }
}
