// Visitor interface for unitary operations
package SyntaxJava.DisqDesign.Syntax.DisQ;

interface UnitaryExprVisitor {
    void visit(Hadamard hadamard);
    void visit(QuantumFourierTransform qft);
    void visit(RotationZ rz);
    void visit(PauliX x);
    void visit(ControlledNot cx);
    void visit(ControlledU cu);
}

