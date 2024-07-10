package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * This interface defines the 'Action' structure within the DisQ framework.
 * It declares a method to accept visitors that implement the ActionVisitor interface,
 * enabling the visitor pattern used to process actions in a structured manner.
 */
public interface Action {
    /**
     * Method to accept a visitor that performs operations defined in ActionVisitor.
     * @param visitor The visitor that implements ActionVisitor to handle the action.
     */
    abstract void accept(ActionVisitor visitor);
}
