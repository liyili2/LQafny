package SyntaxJava.DisqDesign.Syntax.DisQ;

class RotationZ extends UnitaryExpr {
    
    int qubitIndex ;
    double theta ;

    public RotationZ(int qubitIndex , double theta)
    {
        this.qubitIndex=qubitIndex;
        this.theta=theta;
    }
    void accept(UnitaryExprVisitor visitor) {
        visitor.visit(this);
    }
}
