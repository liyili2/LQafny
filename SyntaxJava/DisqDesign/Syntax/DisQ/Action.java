package SyntaxJava.DisqDesign.Syntax.DisQ;


public interface Action {
    abstract void accept(ActionVisitor visitor);
}
