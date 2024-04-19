// Abstract class for unitary expressions
package SyntaxJava.DisqDesign.Syntax.DisQ;


abstract class UnitaryExpr {
    abstract void accept(UnitaryExprVisitor visitor);
}