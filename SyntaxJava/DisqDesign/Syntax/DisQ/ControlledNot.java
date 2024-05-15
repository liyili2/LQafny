package SyntaxJava.DisqDesign.Syntax.DisQ;

class ControlledNot extends UnitaryExpr {
    int control , target ; 
    public ControlledNot(int control , int target)
    {
        this.control = control;
        this.target = target;
    }

    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
