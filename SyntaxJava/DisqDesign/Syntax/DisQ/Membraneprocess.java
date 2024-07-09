package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Membraneprocess implements Membrane {
    private String location;  // Identifier for the membrane's location
    private List<Process> processes;  // List of processes within this membrane
    private Process airlockedProcess;  // Represents an airlocked process if any
    private QuantumState  quantumstate = new QuantumState();
    private QuantumState1 quantumstate1 = new QuantumState1();
    private String message;

    public Membraneprocess() {
       // this.location = location;
        this.processes = new ArrayList<>();
        this.airlockedProcess = null;
    }

    public Membraneprocess(String location) {
        this.location = location;
        this.processes = new ArrayList<>();
        this.airlockedProcess = null;
        this.quantumstate = new QuantumState() ;
        this.quantumstate1 = new QuantumState1() ;
    }

    public void Addqubits(Locus locus , Qubit qubit,String location , double prob)
    {
       // double processProbability = getProcessProbability();
       // quantumstate.SaddQubit(locus, qubit, location, processProbability);
        quantumstate1.addQubit(locus, qubit, location, prob);
  
    }

    public void printQS()
    {
        quantumstate1.printStateVector();
    }
    public QuantumState1 getQuantumState()
    {
        return quantumstate1;
    }
    public int getnumberofqubits()
    {
        return quantumstate.getnumberofqubits();
    }
    

    public void receiveMessage(String message) {
        this.message = message;
        System.out.println("Message received at " + location + ": " + message);
    }

    public String getReceivedMessage() {
        return message;
    }

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

    public void addProcess(Process process) {
        processes.add(process);
    }

    public void airlockProcess(Process process) {
        this.airlockedProcess = process;
    }

    public String getLocation() {
        return location;
    }

    public List<Process> getProcesses() {
        return processes;
    }

    public Process getAirlockedProcess() {
        return airlockedProcess;
    }

    public double getProcessProbability() {
        if (processes.isEmpty()) {
            return 0.0;
        }
        return 1.0 / processes.size();
    }


    @Override
    public void accept(MembraneVisitor visitor) {
        visitor.visit(this);
    }
}
