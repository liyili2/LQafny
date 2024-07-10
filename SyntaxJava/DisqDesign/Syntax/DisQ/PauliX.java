package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents the Pauli-X gate operation as a UnitaryExpr.
 * Extends UnitaryExpr and implements accept method for visitor pattern.
 */
class PauliX extends UnitaryExpr {
    int qubitIndex;  // Index of the qubit to apply Pauli-X gate

    /**
     * Constructor to initialize the Pauli-X gate with a specific qubit index.
     * @param qubitIndex The index of the qubit to apply the Pauli-X gate.
     */
    PauliX(int qubitIndex) {
        this.qubitIndex = qubitIndex;
    }

    /**
     * Accepts a visitor and allows it to visit this Pauli-X gate operation.
     * Calls the visit method specific to PauliX in the visitor.
     * @param visitor The UnitaryExprVisitor visiting this Pauli-X gate.
     */
    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
