package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents a quantum channel creation process between two membranes.
 * Implements the Membrane interface.
 */
public class QuantumChannelcreation implements Membrane {

    private Membraneprocess source;      // Source membrane for the quantum channel
    private Membraneprocess partner;     // Partner membrane for the quantum channel
    private int numQubits;               // Number of qubits involved in the quantum channel

    /**
     * Constructor for QuantumChannelcreation.
     * Initializes the source membrane, partner membrane, and number of qubits.
     * @param source The source membrane.
     * @param partner The partner membrane.
     * @param numQubits Number of qubits for the quantum channel.
     */
    QuantumChannelcreation(Membraneprocess source, Membraneprocess partner, int numQubits) {
        this.source = source;
        this.partner = partner;
        this.numQubits = numQubits;
    }

    /**
     * Sends signals or messages to the partner membrane.
     * @param signals The signals/messages to send.
     */
    public void sendsignals(String signals) {
        partner.receiveMessage(signals);
    }

    /**
     * Creates an EPR pair between the source and partner membranes.
     * @param source The source membrane.
     * @param partner The partner membrane.
     * @param numQubits Number of qubits for the EPR pair creation.
     */
    public void createEPRPair(Membraneprocess source, Membraneprocess partner, int numQubits) {
        for (int i = 0; i < numQubits; i++) {
            // Create qubits for the EPR pair
            Qubit q1 = new Qubit(new Complex(1 / Math.sqrt(2), 0), new Complex(1 / Math.sqrt(2), 0));
            Qubit q2 = new Qubit(new Complex(1 / Math.sqrt(2), 0), new Complex(1 / Math.sqrt(2), 0));
            
            // Assign loci for qubits in source and partner membranes
            Locus sourceloci = new Locus(source.getnumberofqubits());
            Locus partnerloci = new Locus(partner.getnumberofqubits());
            
            // Add qubits to respective membranes
            source.Addqubits(sourceloci, q1, "source", 0.25);
            partner.Addqubits(partnerloci, q2, "target", 0.25);
        }
        System.out.println("EPR pair created between " + source.getLocation() + " and " + partner.getLocation());
    }

    @Override
    public void accept(MembraneVisitor visitor) {
        visitor.visit(this);
    }

    public Membraneprocess getSource() {
     return source;   }

    public Membraneprocess getPartner() {
        return partner; }

    public int getNumQubits() {
       return numQubits;   }
}
