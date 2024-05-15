package SyntaxJava.DisqDesign.Syntax.DisQ;

class PauliX extends UnitaryExpr {
    int qubitIndex;

    PauliX (int qubitIndex)
    {
        this.qubitIndex=qubitIndex;
    }
    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}