package DisqDesign.Syntax;


import DisqDesign.Syntax.SynKinds.*;
import java.util.HashMap;
import java.util.Map;

public class Semantics {

    private SynLoci.TypeEnvironment typeEnvironment;
    private SynLoci.QuantumState quantumState;

    public Semantics(SynLoci.TypeEnvironment typeEnvironment, SynLoci.QuantumState quantumState) {
        this.typeEnvironment = typeEnvironment;
        this.quantumState = quantumState;
    }

    // Simulates the S-MEM semantic rule which could represent a memory operation in the quantum system
    public void sMem(SynLoci.GlobalLocus globalLocus, SynKinds.QuantumValue value, String operation) {
        switch (operation) {
            case "R": // Read operation
                SynKinds.QuantumValue storedValue = quantumState.getState().get(globalLocus);
                System.out.println("Performed read operation. Value: " + storedValue);
                break;
            case "T": // Transform operation
                quantumState.getState().put(globalLocus, value);
                System.out.println("Performed transform operation. Updated value at locus.");
                break;
            default:
                throw new IllegalArgumentException("Unsupported operation type: " + operation);
        }
    }

  
}
