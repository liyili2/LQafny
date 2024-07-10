package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * The ClassicalChannel class represents a communication channel for classical information transfer.
 * This class provides the functionality to send and receive messages, simulating a classical communication
 * channel in a quantum computing context. Each channel is uniquely identified to facilitate specific message routing.
 */
public class ClassicalChannel {
    private String identifier;  // Unique identifier for the channel, used to differentiate among multiple channels.

    /**
     * Constructor for the ClassicalChannel class.
     * Initializes a new instance of a classical channel with a unique identifier.
     * @param identifier A unique string that identifies the channel.
     */
    public ClassicalChannel(String identifier) {
        this.identifier = identifier;
    }

    /**
     * Sends a message over this classical channel.
     * This method simulates the transmission of a message over a classical communication channel,
     * typically used in distributed quantum computing to synchronize operations or convey classical data.
     * @param message The message to be sent over the channel.
     */
    public void send(String message) {
        
        System.out.println("Sending message: " + message + " over channel: " + identifier);
    }

    /**
     * Receives a message from this classical channel.
     * This method simulates the reception of a message from a classical channel.
     * It can be used to simulate receiving synchronization signals or other classical data necessary for quantum operations.
     * @return Returns the simulated received message.
     */
    public String receive() {
        
        System.out.println("Receiving message from channel: " + identifier);
        return "Received Message";  // Simulated response for demonstration purposes.
    }

    /**
     * Gets the identifier of the channel.
     * This identifier is used to reference the channel in communications and can be used to debug or log message routing.
     * @return The unique identifier of the channel.
     */
    public String getIdentifier() {
        return identifier;
    }
}
