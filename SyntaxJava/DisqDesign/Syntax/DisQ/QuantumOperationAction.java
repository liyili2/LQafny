package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents a quantum operation action, such as applying a gate or transformation.
 * Implements the Action interface.
 */
public class QuantumOperationAction implements Action {
    private UnitaryExpr operation; // The quantum operation to be performed
    public int qubitIndex; // Index of the qubit (for single qubit operations)
    public int control; // Control qubit index (for controlled operations)
    public int target; // Target qubit index (for controlled operations)
    public double theta; // Angle parameter (for operations like Rotation Z)

    /**
     * Constructs a QuantumOperationAction for a single qubit operation.
     * @param operation The quantum operation to be performed.
     * @param qubitIndex Index of the qubit.
     */
    public QuantumOperationAction(UnitaryExpr operation, int qubitIndex) {
        this.operation = operation;
        this.qubitIndex = qubitIndex;
    }

    /**
     * Constructs a QuantumOperationAction for an operation with an angle parameter (like Rotation Z).
     * @param operation The quantum operation to be performed.
     * @param qubitIndex Index of the qubit.
     * @param theta Angle parameter.
     */
    public QuantumOperationAction(UnitaryExpr operation, int qubitIndex, double theta) {
        this.operation = operation;
        this.qubitIndex = qubitIndex;
        this.theta = theta;
    }

    /**
     * Constructs a QuantumOperationAction for a controlled operation.
     * @param operation The quantum operation to be performed.
     * @param control Control qubit index.
     * @param target Target qubit index.
     */
    public QuantumOperationAction(UnitaryExpr operation, int control, int target) {
        this.operation = operation;
        this.control = control;
        this.target = target;
    }

    /**
     * Retrieves the quantum operation.
     * @return The quantum operation.
     */
    public UnitaryExpr getOperation() {
        return operation;
    }

    /**
     * Retrieves the qubit index for single qubit operations.
     * @return Qubit index.
     */
    public int getQubitIndex() {
        return qubitIndex;
    }

    /**
     * Retrieves the control qubit index for controlled operations.
     * @return Control qubit index.
     */
    public int getControl() {
        return control;
    }

    /**
     * Retrieves the target qubit index for controlled operations.
     * @return Target qubit index.
     */
    public int getTarget() {
        return target;
    }

    /**
     * Retrieves the angle parameter for operations like Rotation Z.
     * @return Angle parameter.
     */
    public double getTheta() {
        return theta;
    }

    /**
     * Accepts a visitor to perform operations specific to quantum operation actions.
     * @param visitor The visitor implementing ActionVisitor.
     */
    @Override
    public void accept(ActionVisitor visitor) {
        visitor.visit(this);
    }
}
