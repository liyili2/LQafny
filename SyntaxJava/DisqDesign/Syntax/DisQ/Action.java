package SyntaxJava.DisqDesign.Syntax.DisQ;

// Action interface for visitor pattern
public interface Action {
    abstract void accept(ActionVisitor visitor);
}
