package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents a rotation around the Z-axis (Phase rotation) applied to a qubit.
 * Extends UnitaryExpr indicating it's a type of unitary quantum operation.
 */
class RotationZ extends UnitaryExpr {
    int qubitIndex; // Index of the qubit on which rotation is applied
    double theta;   // Rotation angle in radians

    /**
     * Constructor for initializing the RotationZ operation with a specific qubit index and rotation angle.
     * @param qubitIndex Index of the qubit to apply the rotation to.
     * @param theta Rotation angle in radians.
     */
    public RotationZ(int qubitIndex, double theta) {
        this.qubitIndex = qubitIndex;
        this.theta = theta;
    }

    /**
     * Accepts a visitor and invokes the appropriate visit method for this RotationZ operation.
     * @param visitor The visitor object visiting this RotationZ operation.
     */
    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
