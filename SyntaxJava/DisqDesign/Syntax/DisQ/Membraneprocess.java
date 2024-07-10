package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Represents a membrane process within a quantum distributed system.
 * This class manages quantum states, processes, and interaction with visitors.
 */
public class Membraneprocess implements Membrane {

    private String location;  // Identifier for the membrane's location
    private List<Process> processes;  // List of processes within this membrane
    private Process airlockedProcess;  // Represents an airlocked process if any
    private QuantumState1 quantumstate1;  // Quantum state representation using QuantumState1
    private String message;  // Message received by the membrane

    /**
     * Default constructor initializing lists and variables.
     */
    public Membraneprocess() {
        this.processes = new ArrayList<>();
        this.airlockedProcess = null;
        
        this.quantumstate1 = new QuantumState1();
    }

    /**
     * Constructor to initialize with a specific location.
     * @param location The identifier for the membrane's location.
     */
    public Membraneprocess(String location) {
        this.location = location;
        this.processes = new ArrayList<>();
        this.airlockedProcess = null;
        
        this.quantumstate1 = new QuantumState1();
    }

    /**
     * Adds a qubit to the quantum state in this membrane.
     * @param locus The locus (position) of the qubit.
     * @param qubit The qubit object to add.
     * @param location The location identifier within the membrane.
     * @param prob The probability associated with the qubit.
     */
    public void Addqubits(Locus locus, Qubit qubit, String location, double prob) {
        quantumstate1.addQubit(locus, qubit, location, prob);
    }

    /**
     * Prints the state vector of the quantum state represented by QuantumState1.
     */
    public void printQS() {
        quantumstate1.printStateVector();
    }

    /**
     * Retrieves the quantum state represented by QuantumState1.
     * @return The QuantumState1 object representing the quantum state.
     */
    public QuantumState1 getQuantumState() {
        return quantumstate1;
    }

    public int getnumberofqubits()
    {
        return quantumstate1.getnumberofqubits();
    }


    /**
     * Receives a message and stores it within the membrane.
     * @param message The message received.
     */
    public void receiveMessage(String message) {
        this.message = message;
        System.out.println("Message received at " + location + ": " + message);
    }

    /**
     * Retrieves the last received message by the membrane.
     * @return The last received message.
     */
    public String getReceivedMessage() {
        return message;
    }

    /**
     * Teleports a qubit from a source membrane to a target membrane.
     * @param sourceMembrane The source membrane from which to teleport the qubit.
     * @param targetMembrane The target membrane to which the qubit will be teleported.
     * @param qubitIndex The index of the qubit to teleport.
     */
    private void teleportQubit(Membraneprocess sourceMembrane, Membraneprocess targetMembrane, int qubitIndex) {
        QuantumState1 sourceState = sourceMembrane.getQuantumState();
        QuantumState1 targetState = targetMembrane.getQuantumState();

        // Simulate teleportation by copying the state from source to target
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>(targetState.getStateVector());
        sourceState.getStateVector().forEach((state, pair) -> {
            if (state.charAt(qubitIndex) == '1') {
                String newState = state.substring(0, qubitIndex) + '1' + state.substring(qubitIndex + 1);
                newStateVector.merge(newState, new Pair<>(pair.getKey(), targetMembrane.getLocation()), (oldVal, newVal) -> new Pair<>(oldVal.getKey().add(newVal.getKey()), newVal.getValue()));
            }
        });

        targetState.setStateVector(newStateVector);
        targetState.normalizeStateVector();
    }

    /**
     * Adds a process to the list of processes within the membrane.
     * @param process The process to add.
     */
    public void addProcess(Process process) {
        processes.add(process);
    }

    /**
     * Airlocks (selects) a process within the membrane for execution.
     * @param process The process to airlock.
     */
    public void airlockProcess(Process process) {
        this.airlockedProcess = process;
    }

    /**
     * Retrieves the location identifier of the membrane.
     * @return The location identifier.
     */
    public String getLocation() {
        return location;
    }

    /**
     * Retrieves the list of processes within the membrane.
     * @return The list of processes.
     */
    public List<Process> getProcesses() {
        return processes;
    }

    /**
     * Retrieves the airlocked process within the membrane, if any.
     * @return The airlocked process.
     */
    public Process getAirlockedProcess() {
        return airlockedProcess;
    }

    /**
     * Calculates the probability associated with executing any process within the membrane.
     * @return The probability of executing any process.
     */
    public double getProcessProbability() {
        if (processes.isEmpty()) {
            return 0.0;
        }
        return 1.0 / processes.size();
    }

    /**
     * Accepts a visitor for visiting this membrane process.
     * @param visitor The MembraneVisitor to accept.
     */
    @Override
    public void accept(MembraneVisitor visitor) {
        visitor.visit(this);
    }
}
