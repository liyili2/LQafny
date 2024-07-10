package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * The ActionVisitor interface defines the methods required to visit different types
 * of actions in a quantum computing context. It provides a framework for implementing the visitor pattern,
 * which allows operations to be performed on objects without changing the classes on which they operate.
 * Each method is tailored to handle a specific type of action, enabling the separation of algorithm
 * from object structure.
 */
public interface ActionVisitor {
    /**
     * Visits a QuantumOperationAction. This method is intended for implementing
     * logic specific to quantum operations, such as applying quantum gates or transformations.
     * @param action The quantum operation action to process.
     */
    void visit(QuantumOperationAction action);

    /**
     * Visits a ClassicalSendAction. This method handles the logic for sending messages
     * over classical channels, commonly used for synchronization or sending instructions in quantum networks.
     * @param action The classical send action to process.
     */
    void visit(ClassicalSendAction action);

    /**
     * Visits a ClassicalReceiveAction. This method is used for receiving messages from classical channels,
     * essential for operations that depend on classical data inputs or synchronization signals.
     * @param action The classical receive action to process.
     */
    void visit(ClassicalReceiveAction action);

    /**
     * Visits a QuantumMeasurementAction. This method deals with the measurement of quantum states,
     * which is a fundamental aspect of quantum computation and necessary for collapsing quantum states into classical bits.
     * @param action The quantum measurement action to process.
     */
    void visit(QuantumMeasurementAction action);
}
