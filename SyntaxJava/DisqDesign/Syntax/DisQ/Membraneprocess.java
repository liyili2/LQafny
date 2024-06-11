package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.ArrayList;
import java.util.List;

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
