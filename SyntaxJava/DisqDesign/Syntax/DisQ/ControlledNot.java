package SyntaxJava.DisqDesign.Syntax.DisQ;

class ControlledNot extends UnitaryExpr {
    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
