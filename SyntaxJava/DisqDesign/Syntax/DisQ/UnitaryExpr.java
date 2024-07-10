// Abstract class for unitary expressions in quantum computation
package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Abstract class representing a unitary expression in quantum computation.
 * Unitary expressions are operations that preserve the normalization of quantum states.
 */
abstract class UnitaryExpr {

    /**
     * Accepts a visitor for visiting this unitary expression.
     * @param visitor The visitor object that visits this unitary expression.
     */
    abstract void accept(UnitaryExprVisitor visitor);
}
