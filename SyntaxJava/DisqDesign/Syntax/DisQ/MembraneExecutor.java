package SyntaxJava.DisqDesign.Syntax.DisQ;

public class MembraneExecutor implements MembraneVisitor {

    private ProcessVisitor processVisitor ;

    public MembraneExecutor(ProcessVisitor processVisitor) {
        this.processVisitor = processVisitor;
    }

    @Override
    public void visit(Membraneprocess membrane) 
    {
        if (membrane.getAirlockedProcess() != null) {
            // If there is an airlocked process, only it is processed
            membrane.getAirlockedProcess().accept(processVisitor);
        } //else if (membrane.getProcesses() !=null) {
            // Otherwise, all processes are processed
            for (Process process : membrane.getProcesses()) {
                process.accept(processVisitor);
           // }
        }
    }


   
    @Override
    public void visit(QuantumChannelcreation membrane) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'visit'");
    }
    
}
