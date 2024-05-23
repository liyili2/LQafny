package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.HashMap;
import java.util.List;
import java.util.function.BiConsumer;

public class FunctionHandler {
    private HashMap<String, BiConsumer<QuantumState, List<Integer>>> functionMap;

    public FunctionHandler() {
        this.functionMap = new HashMap<>();
        setupFunctions();
    }

    private void setupFunctions() {
        functionMap.put("hadamard", (qs, args) -> qs.applyHadamardToQubit(args.get(0)));
        functionMap.put("pauliX", (qs, args) -> qs.applyXgate(args.get(0)));
        functionMap.put("cnot", (qs, args) -> qs.applyControlXgate(args.get(0), args.get(1)));
        
    }

    public void callFunction(String functionName, QuantumState qs, List<Integer> args) {
        if (functionMap.containsKey(functionName)) {
            functionMap.get(functionName).accept(qs, args);
        } else {
            System.out.println("Function not defined: " + functionName);
        }
    }
}
