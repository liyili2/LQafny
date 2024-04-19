package SyntaxJava.DisqDesign.Syntax.DisQ;

class RotationZ extends UnitaryExpr {
    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
