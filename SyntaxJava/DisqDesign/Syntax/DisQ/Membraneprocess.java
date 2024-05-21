package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.ArrayList;
import java.util.List;

public class Membraneprocess implements Membrane {
    private String location;  // Identifier for the membrane's location
    private List<Process> processes;  // List of processes within this membrane
    private Process airlockedProcess;  // Represents an airlocked process if any

    public Membraneprocess(String location) {
        this.location = location;
        this.processes = new ArrayList<>();
        this.airlockedProcess = null;
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

    @Override
    public void accept(MembraneVisitor visitor) {
        visitor.visit(this);
    }
}
