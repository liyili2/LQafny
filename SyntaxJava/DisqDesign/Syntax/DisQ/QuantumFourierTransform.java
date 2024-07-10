package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents a Quantum Fourier Transform (QFT) operation.
 * Extends the UnitaryExpr class.
 */
class QuantumFourierTransform extends UnitaryExpr {

    /**
     * Accepts a visitor to perform operations specific to Quantum Fourier Transform.
     * @param visitor The visitor implementing UnitaryExprVisitor.
     */
    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
