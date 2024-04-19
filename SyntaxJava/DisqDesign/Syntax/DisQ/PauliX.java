package SyntaxJava.DisqDesign.Syntax.DisQ;

class PauliX extends UnitaryExpr {
    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}