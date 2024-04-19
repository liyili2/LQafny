package SyntaxJava.DisqDesign.Syntax.DisQ;

class QuantumFourierTransform extends UnitaryExpr {
    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}