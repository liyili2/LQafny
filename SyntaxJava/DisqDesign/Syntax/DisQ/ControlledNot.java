package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents a Controlled-NOT (CNOT) gate as a subclass of UnitaryExpr.
 * This gate flips the target qubit if the control qubit is in state |1>.
 * It is a fundamental gate in quantum computing for entanglement and quantum information processing.
 */
class ControlledNot extends UnitaryExpr {
    int control; // Index of the control qubit.
    int target;  // Index of the target qubit.

    /**
     * Constructs a Controlled-NOT (CNOT) gate with specified control and target qubit indices.
     * @param control Index of the control qubit.
     * @param target Index of the target qubit.
     */
    public ControlledNot(int control, int target) {
        this.control = control;
        this.target = target;
    }

    /**
     * Accepts a visitor that implements the UnitaryExprVisitor interface.
     * This method allows the visitor to process this Controlled-NOT gate,
     * enabling operations on CNOT gates without changing their classes.
     * @param visitor The visitor that will process this Controlled-NOT gate.
     */
    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this); // Delegate the processing of this CNOT gate to the visitor.
    }
}
