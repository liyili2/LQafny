package SyntaxJava.DisqDesign.Syntax.DisQ;

public class QuantumSim {
    public static void main(String[] args) {
        QuantumState1 qs1 = new QuantumState1();
      //  QuantumState1 qs2 = new QuantumState1();

        // Adding qubits to the first membrane
        qs1.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.25);
        qs1.addQubit(new Locus(1), new Qubit(new Complex(0, 0), new Complex(1, 0)), "membrane1", 0.25);
        qs1.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.25);
        qs1.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.25);

        // Adding qubits to the second membrane
        // qs2.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.25);
        // qs2.addQubit(new Locus(1), new Qubit(new Complex(0, 0), new Complex(1, 0)), "membrane2", 0.25);
        // qs2.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.25);

        // Print initial state vectors
        System.out.println("Initial State Vector for membrane1:");
        qs1.printStateVector();

        // System.out.println("\nInitial State Vector for membrane2:");
        // qs2.printStateVector();

        // Apply Hadamard gate to the first qubit of the first membrane
        qs1.applyHadamardToQubit(0);

        System.out.println("\nState Vector after applying Hadamard to the first qubit of membrane1:");
        qs1.printStateVectorWithProbabilities();

         // Measure the second qubit of the second membrane
         qs1.measureQubit(1);
         qs1.printStateVectorWithProbabilities();


        // System.out.println("\nState Vector after measuring the second qubit of membrane2:");
        // qs2.printStateVectorWithProbabilities();

        // // Print measurement probabilities
        // System.out.println("\nMeasurement probabilities for membrane2:");
        // qs2.printProbabilities();
    }
}
