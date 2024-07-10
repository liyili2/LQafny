package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents an action to receive a message via a classical communication channel in a quantum computing framework.
 * This class encapsulates all the necessary details to perform a receive operation,
 * including the channel from which the message is received and the variable name where the message is stored.
 */
public class ClassicalReceiveAction implements Action {
    private ClassicalChannel channel; // The classical channel from which the message will be received.
    private String variableName; // Variable to store the received data, linking received data to quantum operations or further processing.

    /**
     * Constructs a ClassicalReceiveAction with a specified channel and variable name.
     * @param channel The classical channel used to receive messages.
     * @param variableName The name of the variable where the received message will be stored.
     */
    public ClassicalReceiveAction(ClassicalChannel channel, String variableName) {
        this.channel = channel;
        this.variableName = variableName;
    }

    /**
     * Returns the classical channel associated with this action.
     * @return The classical channel used for receiving messages.
     */
    public ClassicalChannel getChannel() {
        return channel;
    }

    /**
     * Returns the name of the variable where the received message will be stored.
     * This can be used to reference the message in subsequent operations or for logging purposes.
     * @return The name of the variable storing the received message.
     */
    public String getVariableName() {
        return variableName;
    }

    /**
     * Accepts a visitor that implements the ActionVisitor interface.
     * This method allows the action to be processed by different types of visitors,
     * facilitating the visitor pattern which decouples the actions from the operations performed on them.
     * @param visitor The visitor that will process this action.
     */
    @Override
    public void accept(ActionVisitor visitor) {
        visitor.visit(this); // Delegate the processing of this action to the visitor, allowing different implementations of handling received messages.
    }
}
