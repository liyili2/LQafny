package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents a quantum measurement action on specific qubits.
 * Implements the Action interface.
 */
public class QuantumMeasurementAction implements Action {
    private int targetQubits; // Indices of qubits to be measured
    private String resultVariable; // Variable to store measurement results

    /**
     * Constructs a QuantumMeasurementAction object.
     * @param targetQubits Indices of qubits to be measured.
     * @param resultVariable Variable to store measurement results.
     */
    public QuantumMeasurementAction(int targetQubits, String resultVariable) {
        this.targetQubits = targetQubits;
        this.resultVariable = resultVariable;
    }

    /**
     * Retrieves the indices of qubits to be measured.
     * @return Indices of qubits.
     */
    public int getTargetQubits() {
        return targetQubits;
    }

    /**
     * Retrieves the variable name to store measurement results.
     * @return Result variable name.
     */
    public String getResultVariable() {
        return resultVariable;
    }

    /**
     * Accepts a visitor to perform operations specific to quantum measurement action.
     * @param visitor The visitor implementing ActionVisitor.
     */
    @Override
    public void accept(ActionVisitor visitor) {
        visitor.visit(this);
    }
}
