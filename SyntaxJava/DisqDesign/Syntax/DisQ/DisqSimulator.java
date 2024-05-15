package SyntaxJava.DisqDesign.Syntax.DisQ;

//import java.util.Random;

public class DisqSimulator {
    public static void main(String[] args) {



        QuantumState quantumState = new QuantumState();
        quantumState.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0))); // Add first qubit
        quantumState.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0))); // Add second qubit
        quantumState.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0))); // Add THIRD qubit
        quantumState.addQubit(new Locus(3), new Qubit(new Complex(0, 0), new Complex(1, 0))); // Add FOURTH qubit


        // Print states of all qubits
       quantumState.printQubits();
        
        /***** 
        // Normalize 
        quantumState.qubits.get(0).getValue().normalize();
        quantumState.qubits.get(1).getValue().normalize();
        quantumState.qubits.get(2).getValue().normalize();
        quantumState.qubits.get(3).getValue().normalize();

        //Applying Gates to qubit for that locus
        quantumState.applyHadamardToQubit(1);
        quantumState.applyXgate(0);
        quantumState.applyRzToQubit(3,Math.PI / 4);
        quantumState.applyControlXgate(3,0);

        //Printing qubit states
        quantumState.printQubits();
        ***/


        


        //QuantumState qs = new QuantumState();
        //qs.initializeQubits(3); // Initialize a 3-qubit system
        //QuantumValue qv = qs.quantumValues.get(3);
      //  qs.initializeQubits(3); // Initialize a 3-qubit system
        // Create actions
        Hadamard hadamard = new Hadamard(1);  // Assuming target qubit index 0
        PauliX xgate = new PauliX(0);
        RotationZ RZGate = new RotationZ(3, Math.PI/4);
        ControlledNot Cnot = new ControlledNot(3, 0);
        QuantumOperationAction CNOToperation = new QuantumOperationAction(Cnot, 3,0);
        QuantumOperationAction rotationzgate = new QuantumOperationAction(RZGate, 3 , Math.PI/4);
        QuantumOperationAction xgateoperation = new QuantumOperationAction(xgate, 0) ;
        QuantumOperationAction hadamardAction = new QuantumOperationAction(hadamard , 1);

         // Initialize the interpreter
         ActionInterpreter interpreter = new ActionInterpreter(quantumState);
        
         // Execute actions
         interpreter.visit(hadamardAction);
         interpreter.visit(xgateoperation);
        interpreter.visit(rotationzgate);
        interpreter.visit(CNOToperation);
        
         // Print states of all qubits
       quantumState.printQubits();
    

       // qs.printState();

        // Apply a CNOT gate where the first qubit is the control and the second is the target
        //qs.applyCNOT(0, 1);
    
       // qs.printState();




        /** 
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

        
        QuantumState qs = new QuantumState();
    int numQubits = 3;  // Simulate 3 qubits
    qs.initializeQubits(numQubits);

    // Example: Apply Hadamard gate to the first qubit
   // qs.applyHadamard(new int[]{0});

    // Measure the state (for simplicity, this example just prints out amplitudes)
    QuantumValue finalState = qs.quantumValues.get(0);
    for (int i = 0; i < (1 << numQubits); i++) {  // Loop through all possible states
        System.out.println("State |" + Integer.toBinaryString(i) + "> Amplitude: " + finalState.getAmplitude(i));
    }**/
    //int numQubits = 3;  // For a 3-qubit system
       // QuantumState qs = new QuantumState();  // Initialize with zero amplitudes
        //Random rand = new Random();
       // qs.initializeQubits(numQubits);
       // qs.printState();


        // Randomly setting initial complex amplitudes for the quantum state
       /**for (int i = 0; i < (1 << numQubits); i++) {  // 1 << numQubits is 2^numQubits
            float realPart = rand.nextFloat() * 2 - 1;  // Random real part between -1 and 1
            float imagPart = rand.nextFloat() * 2 - 1;  // Random imaginary part between -1 and 1
            Complex amplitude = new Complex(realPart, imagPart);
            qv.setAmplitude(i, amplitude);
        }**/

       
    }
    
}
