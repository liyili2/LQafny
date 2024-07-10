package SyntaxJava.DisqDesign.Syntax.DisQ;

public class QuantumSim {
    public static void main(String[] args) {

      
        DistributedShorsAlgorithm algorithm = new DistributedShorsAlgorithm();
        int N = 241123 ; // Example with N = 15
       
      //  algorithm.factorize(N);
    
       QuantumState1 qs1 = new QuantumState1();
       QuantumState1 qs2 = new QuantumState1();
      // QuantumState1 qs3 = qs2 ;

        //Adding qubits to the first membrane
        qs1.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.25);
        qs1.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.25);
        qs1.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.25);
      //  qs1.addQubit(new Locus(3), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.25);

       // Adding qubits to the second membrane
        qs2.addQubit(new Locus(0), new Qubit(new Complex(0, 0), new Complex(1, 0)), "membrane2", 0.25);
       // qs2.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.25);
        //qs2.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.25);
      //  qs2.addQubit(new Locus(3), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.25);

        QuantumState1 qs3 = qs2 ;
        System.out.println("cc\n");
        qs3.printStateVector();
        System.out.println("123cc\n");
        
        qs3.applyQFT();
        System.out.println("princc\n");
        qs3.printStateVector();

      //   //Print initial state vectors
      //   System.out.println("Initial State Vector for membrane1:");
      //   qs1.printStateVector();
      //   System.out.println("cc\n");
      // //  qs1.applyHadamardToQubit(0);
      //  // qs1.printStateVector();
      //   qs1.applyHadamardToQubit(1);
      //  // qs1.printStateVector();
      // //  qs1.applyHadamardToQubit(2);
      //   qs1.printStateVector();

      //   qs1.measureQubit(0);

      //   qs1.printStateVector();

        // System.out.println("\nInitial State Vector for membrane2:");
        // qs2.printStateVector();

        // qs1.teleportQubit(qs2, 1);

        // System.out.println("\nTeleport State Vector for membrane2:");
        // qs2.printStateVector();
        // System.out.println("----");
        // qs1.printStateVector();

      //  // Apply Hadamard gate to the first qubit of the first membrane
      //  qs1.applyHadamardToQubit(0);
      //  qs1.printStateVectorWithProbabilities();
      //  qs1.applyControlledXToQubit(1,0);

      //   System.out.println("\nState Vector after applying  to the first qubit of membrane1:");
      //   qs1.printStateVectorWithProbabilities();

      //   // Measure the second qubit of the second membrane
      //    qs1.measureQubit(0);
      //    qs1.printStateVectorWithProbabilities();


      //   System.out.println("\nState Vector after measuring the second qubit of membrane2:");
      //   qs2.printStateVectorWithProbabilities();

      //   // Print measurement probabilities
      //   System.out.println("\nMeasurement probabilities for membrane2:");
      //   qs2.printProbabilities();
    }
}
