package SyntaxJava.DisqDesign.Syntax.DisQ;

public class DisqSimulator {
    public static void main(String[] args) {
        // Initialize the quantum state
        QuantumState quantumState = new QuantumState();

        // Create actions
        Hadamard hadamard = new Hadamard(0);  // Assuming target qubit index 0
        QuantumOperationAction hadamardAction = new QuantumOperationAction(hadamard);
        
        ClassicalChannel channel = new ClassicalChannel("channel1");
        ClassicalSendAction sendAction = new ClassicalSendAction(channel, "Hello, quantum world!");

        // Initialize the interpreter
        ActionInterpreter interpreter = new ActionInterpreter(quantumState);
        
        // Execute actions
        interpreter.visit(hadamardAction);
        interpreter.visit(sendAction);

        // Add more actions and tests as needed
    }
    
}
