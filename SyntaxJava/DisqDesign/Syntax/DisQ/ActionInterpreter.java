package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * The ActionInterpreter class implements the ActionVisitor interface and is responsible for
 * executing various types of actions—both quantum and classical—on a given quantum state.
 * It interprets actions by calling appropriate methods on quantum or classical components,
 * allowing for operations like gate application, measurements, and classical communications.
 */
public class ActionInterpreter implements ActionVisitor {
     
    private QuantumState1 quantumState2; // Holds the quantum state object on which operations will be performed.

    /**
     * Constructor to initialize the ActionInterpreter with a specific QuantumState1 instance.
     * This quantum state will be manipulated through various quantum operations defined in the actions visited.
     * @param quantumState2 The quantum state instance to use for operation execution.
     */
    public ActionInterpreter(QuantumState1 quantumState2) {
        this.quantumState2 = quantumState2;
    }

    /**
     * Processes a QuantumOperationAction by applying the specified quantum operation
     * to the quantum state. This method identifies the type of quantum gate or operation
     * encapsulated within the action and applies it to the appropriate qubits.
     * @param action The quantum operation action that specifies the operation and target qubits.
     */
    @Override
    public void visit(QuantumOperationAction action) {
        UnitaryExpr operation = action.getOperation(); // Retrieves the specific quantum operation to perform.
        
        int qubitIndex = action.qubitIndex; // Index of the qubit on which to apply the operation.
        double theta = action.theta; // Parameter for rotation gates, specifies the angle of rotation.
        int control = action.control; // Index of the control qubit for controlled gates.
        int target = action.target; // Index of the target qubit for controlled gates.
        
        // Conditional structure to determine and apply the specific quantum operation.
        if (operation instanceof Hadamard) {
            System.out.println("\nHadamard Gate: \n");
            quantumState2.applyHadamardToQubit(qubitIndex);
            quantumState2.printStateVector(); // Outputs the state of the quantum system post-operation.
        } else if (operation instanceof PauliX) {
            System.out.println("\nX Gate: \n");
            quantumState2.applyXToQubit(qubitIndex);
            quantumState2.printStateVector();
        } else if (operation instanceof QuantumFourierTransform) {
            System.out.println("\nQFT Gate: \n");
            quantumState2.applyQFT(); // Applies the Quantum Fourier Transform to the entire state.
            quantumState2.printStateVector();
        } else if (operation instanceof RotationZ) {
            System.out.println("\nRZ Gate: \n");
            quantumState2.applyRotationZToQubit(qubitIndex, theta);
            quantumState2.printStateVector();
        } else if (operation instanceof ControlledNot) {
            System.out.println("\nCNOT Gate: \n");
            quantumState2.applyControlledXToQubit(control, target);
            quantumState2.printStateVector();
        } 
    }

    /**
     * Interprets a classical send action by transmitting a message through a designated classical channel.
     * This method is key for operations involving classical communication between quantum nodes.
     * @param action The classical send action containing the message and channel details.
     */
    @Override
    public void visit(ClassicalSendAction action) {
        System.out.println("Sending message: " + action.getMessage() + " over channel: " + action.getChannel().getIdentifier());
        action.getChannel().send(action.getMessage()); // Sends the message over the specified classical channel.
    }

    /**
     * Handles a classical receive action by retrieving a message from a specified classical channel.
     * The message is typically used for further operations or stored for record-keeping.
     * @param action The classical receive action detailing the receiving channel and variable storage.
     */
    @Override
    public void visit(ClassicalReceiveAction action) {
        String message = action.getChannel().receive(); // Receives a message from the specified classical channel.
        System.out.println("Received message: " + message + " stored in variable: " + action.getVariableName());
    }

    /**
     * Executes a quantum measurement action by measuring specific qubits within the quantum state.
     * Measurement results can affect subsequent quantum or classical operations.
     * @param action The quantum measurement action specifying the qubits to measure.
     */
    @Override
    public void visit(QuantumMeasurementAction action) {
       String result = quantumState2.measureQubit(action.getTargetQubits()); // Performs measurement on specified qubits.
      System.out.println("Measurement result: " + result);
    }
}
