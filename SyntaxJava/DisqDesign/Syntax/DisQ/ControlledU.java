package SyntaxJava.DisqDesign.Syntax.DisQ;

class ControlledU extends UnitaryExpr {
    UnitaryExpr internalUnitary; // The recursive term for controlled operations

    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
