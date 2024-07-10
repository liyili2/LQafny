package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents an action to send a message via a classical communication channel within a quantum computing context.
 * This class encapsulates the details required to perform a send operation,
 * including the channel used for sending and the actual message to be sent.
 */
public class ClassicalSendAction implements Action {
    private ClassicalChannel channel; // The channel through which the message will be sent.
    private String message; // The message to be sent through the channel.

    /**
     * Constructs a ClassicalSendAction with a specified channel and message.
     * This setup facilitates the transmission of classical data, which can be used for synchronization between quantum processes or other communication needs.
     * @param channel The classical channel used to send the message.
     * @param message The message to be sent over the channel.
     */
    public ClassicalSendAction(ClassicalChannel channel, String message) {
        this.channel = channel;
        this.message = message;
    }

    /**
     * Returns the classical channel used for sending the message.
     * This method provides access to the channel details, potentially useful for logging or further message routing decisions.
     * @return The classical channel through which the message is sent.
     */
    public ClassicalChannel getChannel() {
        return channel;
    }

    /**
     * Returns the message that is sent over the channel.
     * This information is crucial for understanding the content of communications within the system and for debugging purposes.
     * @return The message being sent.
     */
    public String getMessage() {
        return message;
    }

    /**
     * Accepts a visitor that implements the ActionVisitor interface.
     * This method allows the action to be processed by different types of visitors,
     * utilizing the visitor pattern to separate operations from the objects they operate on.
     * @param visitor The visitor that will process this action.
     */
    @Override
    public void accept(ActionVisitor visitor) {
        visitor.visit(this); // Delegate the processing of this action to the visitor, enabling different implementations of send message functionality.
    }
}
