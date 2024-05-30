package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.Arrays;

//import java.util.Random;

public class DisqSimulator {
    public static void main(String[] args) {






      // Initialize the quantum state with 4 qubits for example
        QuantumState quantumState = new QuantumState();
        quantumState.SaddQubit(new Locus(0), new Qubit(new Complex(0.8, 0), new Complex(0.6, 0)));
        quantumState.SaddQubit(new Locus(1), new Qubit(new Complex(0, 0), new Complex(1, 0)));
        quantumState.SaddQubit(new Locus(2), new Qubit(new Complex(0, 0), new Complex(1, 0)));
        // quantumState.SaddQubit(new Locus(3), new Qubit(new Complex(1, 0), new Complex(0, 0)));
       
       
        // quantumState.printStateVector();
        quantumState.normalizeStateVector3();
        quantumState.printStateVector3();
        // quantumState.SaddQubit(new Locus(1), new Qubit(new Complex(0.3, 0), new Complex(0.4, 0)));
        // quantumState.SaddQubit(new Locus(2), new Qubit(new Complex(0.3, 0), new Complex(0.7, 0)));
        // quantumState.SaddQubit(new Locus(3), new Qubit(new Complex(0.7, 0), new Complex(0.3, 0)));
        //quantumState.applyHadamardToQubit(new Locus(1));
       // quantumState.applyHadamardToQubit3(0);
      // System.out.println("Hadamard::::\n");
      // quantumState.printStateVector3();

        // quantumState.applyHadamardToQubit(1);
       //   System.out.println("Xgate ::::\n");
      // quantumState.applyXgate(1);
       // quantumState.printStateVector3();
      System.out.println("Control X \n");
       quantumState.applyControlXgate(1,2);
       quantumState.printStateVector3();

      //  quantumState.qubits.get(0).getValue().normalize();       // quantumState.printStateVector();
      //  quantumState.qubits.get(1).getValue().normalize();
      //  quantumState.qubits.get(2).getValue().normalize();
      //  quantumState.qubits.get(3).getValue().normalize();
        
        //print qubits
        // System.out.println("check\n");
        // quantumState.printQubits();

        // quantumState.measureAndNormalize(new int[] {0});

        //  //print qubits
        //  System.out.println("check_measure\n");
        //  quantumState.printQubits();

        // Initialize the function handler
        //FunctionHandler functionHandler = new FunctionHandler();

        // Example: Apply a Hadamard gate to the first qubit
        //functionHandler.callFunction("hadamard", quantumState, Arrays.asList(0));

        // Example: Apply a CNOT gate between the first and second qubits
        //functionHandler.callFunction("cnot", quantumState, Arrays.asList(0, 1));

        // Print the state of the qubits to verify the operations
        //quantumState.printQubits();



        //Checking.....
        //QuantumState quantumState = new QuantumState();
        //quantumState.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0))); // Add first qubit
       // quantumState.addQubit(new Locus(1), new Qubit(new Complex(0, 0), new Complex(1, 0))); // Add second qubit
       // quantumState.addQubit(new Locus(2), new Qubit(new Complex(0, 0), new Complex(1, 0))); // Add THIRD qubit
       // quantumState.addQubit(new Locus(3), new Qubit(new Complex(0, 0), new Complex(1, 0))); // Add FOURTH qubit
       // quantumState.qubits.get(0).getValue().normalize();
       // quantumState.qubits.get(1).getValue().normalize();
       // quantumState.qubits.get(2).getValue().normalize();
       // quantumState.qubits.get(3).getValue().normalize();
       // quantumState.printQubits();

         // Determine the NOR type
        // String norType = quantumState.NorType();
        
         // Print the NOR type
        // System.out.println("NOR Type: " + norType);


        // quantumState.applyHadamardToQubit(0);
        // quantumState.applyControlXgate(0, 1);
        // quantumState.printQubits();
       // quantumState.lprintTensorProduct();
      //   quantumState.printQubits();

          //  quantumState.ENType(0,1);
         //   quantumState.printQubits();
            // Determine the NOR type
        //  norType = quantumState.NorType();
        
         // Print the NOR type
        // System.out.println("NOR Type: " + norType);




        // Print states of all qubits
       //quantumState.printQubits();
       //quantumState.printTensorProduct();
      // quantumState.tensornorm();
        
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
       //  ActionInterpreter interpreter = new ActionInterpreter(quantumState);
        
         // Execute actions
        // interpreter.visit(hadamardAction);
         //interpreter.visit(xgateoperation);
        //interpreter.visit(rotationzgate);
        //interpreter.visit(CNOToperation);
        
       // ProcessExecutor executor = new ProcessExecutor(quantumState);
       // Process NoOpera = new NoOp ();
       // Process SecPro = new SequentialProcess ( CNOToperation , NoOpera );
       // Process OnePro = new SequentialProcess ( hadamardAction , SecPro ) ;
        

       // OnePro.accept(executor);

       // ConditionalProcess condProc = new ConditionalProcess (()->false,SecPro,NoOpera);
       // condProc.accept(executor);
        //Membrane
        Membraneprocess membrane = new Membraneprocess("membran1");
       // Locus loci = new Locus(1);
        membrane.Addqubits(new Locus(0), new Qubit(new Complex(0, 0), new Complex(1, 0)));
        membrane.Addqubits(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)));
        membrane.Addqubits(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)));
        membrane.Addqubits(new Locus(3), new Qubit(new Complex(0, 0), new Complex(1, 0)));
       
        Membraneprocess membrane2 = new Membraneprocess("membrane2");
        // Locus loci = new Locus(1);
         membrane2.Addqubits(new Locus(0), new Qubit(new Complex(0, 0), new Complex(1, 0)));
         membrane2.Addqubits(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)));
         membrane2.Addqubits(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)));
         membrane2.Addqubits(new Locus(3), new Qubit(new Complex(0, 0), new Complex(1, 0)));
        
        ProcessExecutor executor = new ProcessExecutor(membrane.getQuantumState());
        Process NoOpera = new NoOp ();
        Process SecPro = new SequentialProcess ( CNOToperation , NoOpera );
        Process OnePro = new SequentialProcess ( hadamardAction , SecPro ) ;
        membrane.addProcess(OnePro); // Assuming QuantumOperationAction implements Process
        membrane.airlockProcess(NoOpera); // Assuming ClassicalSendAction implements Process
        membrane2.addProcess(OnePro); // Assuming QuantumOperationAction implements Process
        membrane2.airlockProcess(NoOpera); // Assuming ClassicalSendAction implements Process


        ProcessVisitor processVisitor = new ProcessExecutor(membrane.getQuantumState()); // Assuming ProcessExecutor implements ProcessVisitor
        ProcessVisitor processVisitor2 = new ProcessExecutor(membrane2.getQuantumState()); // Assuming ProcessExecutor implements ProcessVisitor
       
        MembraneVisitor membraneVisitor = new MembraneExecutor(processVisitor);
        MembraneVisitor membraneVisitor2 = new MembraneExecutor(processVisitor2);

      // membrane.accept(membraneVisitor); // Execute visitor on the membrane
      // membrane2.accept(membraneVisitor2); // Execute visitor on the membrane
      
       QuantumChannelcreation channel = new QuantumChannelcreation(membrane, membrane2, 1);
       channel.sendsignals("Hello");


       // System.out.println("\nSize of qubits:"+membrane.getnumberofqubits());
    
            
         // Print states of all qubits
      // quantumState.printQubits();
    

       // qs.printState);

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
