// Visitor interface for unitary operations in quantum computation
package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Interface defining a visitor for unitary operations in quantum computation.
 * Each method corresponds to visiting a specific type of unitary operation.
 */
interface UnitaryExprVisitor {

    /**
     * Visits a Hadamard gate operation.
     * @param hadamard The Hadamard gate object to visit.
     */
    void visit(Hadamard hadamard);

    /**
     * Visits a Quantum Fourier Transform (QFT) operation.
     * @param qft The QFT operation object to visit.
     */
    void visit(QuantumFourierTransform qft);

    /**
     * Visits a RotationZ gate operation.
     * @param rz The RotationZ gate object to visit.
     */
    void visit(RotationZ rz);

    /**
     * Visits a PauliX gate operation.
     * @param x The PauliX gate object to visit.
     */
    void visit(PauliX x);

    /**
     * Visits a ControlledNot gate operation.
     * @param cx The ControlledNot gate object to visit.
     */
    void visit(ControlledNot cx);
}
