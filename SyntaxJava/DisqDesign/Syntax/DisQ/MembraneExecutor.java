package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Implementation of a membrane visitor that executes processes within membranes.
 */
public class MembraneExecutor implements MembraneVisitor {

    private ProcessVisitor processVisitor;

    /**
     * Constructs a MembraneExecutor with a given process visitor.
     * @param processVisitor The process visitor to use for executing processes.
     */
    public MembraneExecutor(ProcessVisitor processVisitor) {
        this.processVisitor = processVisitor;
    }

    /**
     * Visits a Membrane process and executes its airlocked process or all processes if no airlocked process exists.
     * @param membrane The Membrane process to visit.
     */
    @Override
    public void visit(Membraneprocess membrane) {
        if (membrane.getAirlockedProcess() != null) {
            membrane.getAirlockedProcess().accept(processVisitor);
        } else {
            for (Process process : membrane.getProcesses()) {
                process.accept(processVisitor);
            }
        }
    }

    /**
     * Placeholder method for visiting Quantum Channel creation membranes.
     * @param membrane The Quantum Channel creation membrane to visit.
     */
    @Override
    public void visit(QuantumChannelcreation membrane) {
        membrane.createEPRPair(membrane.getSource(), membrane.getPartner(), membrane.getNumQubits());
    }
}
