package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents a Hadamard gate operation in quantum computing.
 * Extends UnitaryExpr and implements accept method to support visitor pattern.
 */
class Hadamard extends UnitaryExpr {
    int qubitIndex; // Index of the qubit to apply the Hadamard gate
    QuantumValue quantumValue; // Quantum value associated with the Hadamard gate (optional)

    /**
     * Constructs a Hadamard gate operation for a specific qubit index.
     * @param qubitIndex The index of the qubit to apply the Hadamard gate.
     * @param quantumValue The quantum value associated with the Hadamard gate.
     */
    public Hadamard(int qubitIndex, QuantumValue quantumValue) {
        this.qubitIndex = qubitIndex;
        this.quantumValue = quantumValue;
    }

    /**
     * Constructs a Hadamard gate operation for a specific qubit index.
     * @param qubitIndex The index of the qubit to apply the Hadamard gate.
     */
    public Hadamard(int qubitIndex) {
        this.qubitIndex = qubitIndex;
    }

    /**
     * Retrieves the index of the qubit to which the Hadamard gate is applied.
     * @return The index of the qubit.
     */
    public int getqubitIndex() {
        return qubitIndex;
    }

    /**
     * Retrieves the quantum value associated with the Hadamard gate.
     * @return The quantum value associated with the Hadamard gate.
     */
    public QuantumValue getquantumvalues() {
        return quantumValue;
    }

    /**
     * Accepts a visitor for the visitor pattern implementation.
     * Calls the visit method of the visitor to process this Hadamard gate.
     * @param visitor The visitor object to accept.
     */
    @Override
    public void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
