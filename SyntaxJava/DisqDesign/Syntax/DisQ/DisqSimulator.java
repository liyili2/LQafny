// Main simulation class for DisQ quantum computation framework
package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.Arrays;

/**
 * This class demonstrates a simulation of quantum computation processes using the DisQ framework.
 */
public class DisqSimulator {

    public static void main(String[] args) {
        // Initialize quantum state with 4 qubits, each initialized to |0>
        QuantumState1 quantumState = new QuantumState1();
        quantumState.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "1stqubit", 0.25);
        quantumState.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "1stqubit", 0.25);
        quantumState.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "1stqubit", 0.25);
        quantumState.addQubit(new Locus(3), new Qubit(new Complex(1, 0), new Complex(0, 0)), "1stqubit", 0.25);

       
        

        // Example quantum operations
        Hadamard hadamard = new Hadamard(1);  // Apply Hadamard gate on qubit index 1
        PauliX xgate = new PauliX(0);        // Apply PauliX gate on qubit index 0
        RotationZ RZGate = new RotationZ(3, Math.PI / 4);  // Apply RotationZ gate on qubit index 3
        ControlledNot Cnot = new ControlledNot(3, 0);       // Apply CNOT gate with control qubit 3 and target qubit 0

        // Create quantum operation actions
        QuantumOperationAction CNOToperation = new QuantumOperationAction(Cnot, 3, 0);
        QuantumOperationAction rotationzgate = new QuantumOperationAction(RZGate, 3, Math.PI / 4);
        QuantumOperationAction xgateoperation = new QuantumOperationAction(xgate, 0);
        QuantumOperationAction hadamardAction = new QuantumOperationAction(hadamard, 1);

        // Classical channel and action example
        ClassicalChannel channel = new ClassicalChannel("channel1");
        ClassicalSendAction sendAction = new ClassicalSendAction(channel, "Hello, quantum world!");

        // Initialize action interpreter with the initial quantum state
        ActionInterpreter interpreter = new ActionInterpreter(quantumState);

        // Execute quantum operations
        interpreter.visit(hadamardAction);
        interpreter.visit(xgateoperation);
        interpreter.visit(rotationzgate);
        interpreter.visit(CNOToperation);

        // Function quantum state example
        QuantumState1 qs_function = new QuantumState1();
        qs_function.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "function", 0.25);
        qs_function.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "function", 0.25);
        qs_function.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "function", 0.25);
        qs_function.addQubit(new Locus(3), new Qubit(new Complex(1, 0), new Complex(0, 0)), "function", 0.25);

        // Example function handler
        FunctionHandler functionHandler = new FunctionHandler();

        // Example: Apply a Hadamard gate to the first qubit
        functionHandler.callFunction("hadamard", qs_function, Arrays.asList(0));

        // Example: Apply a CNOT gate between the first and second qubits
        functionHandler.callFunction("cnot", qs_function, Arrays.asList(0, 1));

        // Print the state of the qubits to verify the operations
        System.out.println("Function Handler");
        qs_function.printStateVector();

        // Example membrane processes
        Membraneprocess membrane = new Membraneprocess("membran1");
        membrane.Addqubits(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membranel", 0.25);
        membrane.Addqubits(new Locus(1), new Qubit(new Complex(0, 0), new Complex(1, 0)), "membranel", 0.25);
        membrane.Addqubits(new Locus(2), new Qubit(new Complex(0, 0), new Complex(1, 0)), "membranel", 0.25);
        membrane.Addqubits(new Locus(3), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membranel", 0.25);

        Membraneprocess membrane2 = new Membraneprocess("membrane2");
        membrane2.Addqubits(new Locus(0), new Qubit(new Complex(0, 0), new Complex(1, 0)), "membrane2", 0.25);
        membrane2.Addqubits(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.25);
        membrane2.Addqubits(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.25);
        membrane2.Addqubits(new Locus(3), new Qubit(new Complex(0, 0), new Complex(1, 0)), "membrane2", 0.25);

        // Example process execution
        ProcessExecutor executor = new ProcessExecutor(membrane.getQuantumState());
        Process NoOpera = new NoOp();
        Process SecPro = new SequentialProcess(CNOToperation, NoOpera);
        Process OnePro = new SequentialProcess(hadamardAction, SecPro);
        membrane.addProcess(OnePro);   // Adding a quantum operation process to membrane
        membrane.airlockProcess(NoOpera);  // Airlocking a classical send action to membrane
        membrane2.addProcess(OnePro);  // Adding a quantum operation process to membrane2
        membrane2.airlockProcess(NoOpera);  // Airlocking a classical send action to membrane2

        // Example process visitors
        ProcessVisitor processVisitor = new ProcessExecutor(membrane.getQuantumState());  // Creating a process visitor for membrane
        ProcessVisitor processVisitor2 = new ProcessExecutor(membrane2.getQuantumState());  // Creating a process visitor for membrane2

        MembraneVisitor membraneVisitor = new MembraneExecutor(processVisitor);
        MembraneVisitor membraneVisitor2 = new MembraneExecutor(processVisitor2);

        // Execute visitors on membranes
        membrane.accept(membraneVisitor);  // Accepting visitor on membrane
        membrane2.accept(membraneVisitor2);  // Accepting visitor on membrane2

        // Example quantum channel creation and signal sending
        QuantumChannelcreation channels = new QuantumChannelcreation(membrane, membrane2, 1);
        channels.sendsignals("Hello");  // Sending signals through quantum channels
    }
}
