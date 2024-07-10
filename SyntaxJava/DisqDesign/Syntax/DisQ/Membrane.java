package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Interface representing a membrane in a quantum computing context.
 * It defines a method for accepting a visitor that operates on membranes.
 */
public interface Membrane {
    /**
     * Accepts a visitor that operates on membranes.
     * @param visitor The membrane visitor to accept.
     */
    void accept(MembraneVisitor visitor);
}
