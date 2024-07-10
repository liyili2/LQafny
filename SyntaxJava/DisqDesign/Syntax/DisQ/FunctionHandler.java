package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.HashMap;
import java.util.List;
import java.util.function.BiConsumer;

/**
 * A class to handle and execute quantum functions defined by name with specific arguments on a QuantumState object.
 */
public class FunctionHandler {
    private HashMap<String, BiConsumer<QuantumState1, List<Integer>>> functionMap;

    /**
     * Constructor for FunctionHandler.
     * Initializes the function map and sets up predefined quantum functions.
     */
    public FunctionHandler() {
        this.functionMap = new HashMap<>();
        setupFunctions();
    }

    /**
     * Sets up predefined quantum functions and maps them to their respective names.
     * Each function is represented as a BiConsumer that accepts a QuantumState and a list of arguments.
     */
    private void setupFunctions() {
        // Define and map quantum functions
        functionMap.put("hadamard", (qs, args) -> qs.applyHadamardToQubit(args.get(0)));
        functionMap.put("pauliX", (qs, args) -> qs.applyXToQubit(args.get(0))); 
        functionMap.put("cnot", (qs, args) -> qs.applyControlledXToQubit(args.get(0), args.get(1))); 
        
    }

    /**
     * Calls a quantum function by name with the given quantum state and arguments.
     * @param functionName The name of the quantum function to call.
     * @param qs The QuantumState object on which the function operates.
     * @param args The list of arguments required by the function.
     */
    public void callFunction(String functionName, QuantumState1 qs, List<Integer> args) {
        if (functionMap.containsKey(functionName)) {
            // Retrieve the function from the map and apply it to the quantum state and arguments
            functionMap.get(functionName).accept(qs, args);
        } else {
            // Handle case where function is not defined
            System.out.println("Function not defined: " + functionName);
        }
    }
}
