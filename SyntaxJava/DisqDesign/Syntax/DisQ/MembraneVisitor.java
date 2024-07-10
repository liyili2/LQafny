package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Interface for visiting different types of membranes within a quantum distributed system.
 * Implementations of this interface can visit Membraneprocess and QuantumChannelcreation.
 */
public interface MembraneVisitor {

    /**
     * Method to visit a Membraneprocess.
     * @param membranes The Membraneprocess to visit.
     */
    void visit(Membraneprocess membranes);

    /**
     * Method to visit a QuantumChannelcreation.
     * @param membrane The QuantumChannelcreation to visit.
     */
    void visit(QuantumChannelcreation membrane);
}
