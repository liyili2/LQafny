package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Interface for a process within a membrane or quantum channel.
 * Defines a method for accepting a ProcessVisitor.
 */
interface Process {
    
    /**
     * Accepts a visitor and allows it to visit this process.
     * This method is part of the visitor pattern implementation.
     * @param visitor The ProcessVisitor visiting this process.
     */
    void accept(ProcessVisitor visitor);
}
