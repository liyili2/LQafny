package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.*;

/**
 * Class for simulating and comparing quantum configurations using DisQ.
 */
public class DisQSimulation {

    /**
     * Inner class representing a quantum configuration with state, gates, probability, and measurement results.
     */
    static class Configuration {
        QuantumState1 phi;              // Quantum state
        List<String> gates;             // List of gate operations
        double probability;             // Probability
        String measurementResult;       // Measurement result

        /**
         * Constructor to initialize a configuration with quantum state, gates, and probability.
         * @param phi The quantum state.
         * @param gates List of gate operations.
         * @param probability Probability of the configuration.
         */
        Configuration(QuantumState1 phi, List<String> gates, double probability) {
            this.phi = phi;
            this.gates = gates;
            this.probability = probability;
            this.measurementResult = null; // Initialize measurement result as null
        }

        /**
         * Copy constructor for creating a new Configuration based on an existing one.
         * @param config Existing Configuration to copy.
         */
        Configuration(Configuration config) {
            this.phi = new QuantumState1();
            this.phi.setStateVector(new HashMap<>(config.phi.getStateVector()));
            this.gates = new ArrayList<>(config.gates);
            this.probability = config.probability;
            this.measurementResult = config.measurementResult;
        }

        /**
         * Apply the gates to the quantum state.
         */
        void applyGates() {
            for (String gate : gates) {
                switch (gate) {
                    case "Hadamard":
                        phi.applyHadamardToQubit(0); // Applying Hadamard to the first qubit
                        break;
                    case "CNot":
                        phi.applyControlledXToQubit(0, 1); // Applying CNot with control on the first qubit and target on the second qubit
                        break;
                    // Add other gates as needed
                }
            }
        }

        /**
         * Measure a specific qubit in the quantum state.
         * @param qubitIndex Index of the qubit to measure.
         */
        void measureQubit(int qubitIndex) {
            measurementResult = phi.measureQubit(qubitIndex); // Store measurement result
        }

        /**
         * Override equals method to compare Configuration objects.
         * @param o Object to compare.
         * @return True if objects are equal, false otherwise.
         */
        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Configuration that = (Configuration) o;
            return Double.compare(that.probability, probability) == 0 &&
                    Objects.equals(phi, that.phi) &&
                    Objects.equals(gates, that.gates) &&
                    Objects.equals(measurementResult, that.measurementResult); // Compare measurement results
        }

        /**
         * Override hashCode method.
         * @return Hash code of the Configuration object.
         */
        @Override
        public int hashCode() {
            return Objects.hash(phi, gates, probability, measurementResult);
        }
    }

    /**
     * Main method demonstrating quantum simulation and equivalence checking.
     * @param args Command-line arguments (not used).
     */
    public static void main(String[] args) {
        // Example setup of quantum states G and H
        QuantumState1 stateG = new QuantumState1();
        QuantumState1 stateH = new QuantumState1();

        // Add initial qubits and gates for states G and H
        stateG.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.5);
        stateG.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.5);
        stateG.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.5);
        stateG.addQubit(new Locus(3), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.5);

        stateH.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.5);
        stateH.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.5);
        stateH.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.5);
        stateH.addQubit(new Locus(3), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 0.5);

        stateG.printStateVector();
        stateH.printStateVector();

        // Create configurations for G and H
        Configuration configG = new Configuration(stateG, Arrays.asList("Hadamard", "CNot"), 0.5);
        Configuration configH = new Configuration(stateH, Arrays.asList("Hadamard", "CNot"), 0.5);

        // Apply gates to configurations G and H
        configG.applyGates();
        configH.applyGates();

        // Measure qubits in configurations G and H
        configG.measureQubit(2);
        configH.measureQubit(2);

        // Create sets of configurations G and H for equivalence checking
        Set<Configuration> setG = new HashSet<>(Collections.singleton(configG));
        Set<Configuration> setH = new HashSet<>(Collections.singleton(configH));

        // Check if configurations G and H are not simulation equivalent
        boolean result = notSim(setG, setH);

        // Print simulation result
        System.out.println("Not Simulation result: " + result);
    }

    /**
     * Function to check if sets of configurations G and H are not simulation equivalent.
     * @param G Set of configurations G.
     * @param H Set of configurations H.
     * @return True if G and H are not simulation equivalent, false otherwise.
     */
    private static boolean notSim(Set<Configuration> G, Set<Configuration> H) {
        for (Configuration configG : G) {
            boolean matchFound = false;
            for (Configuration configH : H) {
                if (transitionsMatch(configG, configH)) {
                    matchFound = true;
                    break;
                }
            }
            if (!matchFound) {
                return true;
            }
        }
        return false;
    }

    /**
     * Helper function to compare transitions between two configurations.
     * @param g Configuration G.
     * @param h Configuration H.
     * @return True if transitions between G and H match, false otherwise.
     */
    private static boolean transitionsMatch(Configuration g, Configuration h) {
        if (!g.gates.equals(h.gates) || Double.compare(g.probability, h.probability) != 0) {
            return false;
        }

        Map<String, Pair<Complex, String>> stateVectorG = g.phi.getStateVector();
        Map<String, Pair<Complex, String>> stateVectorH = h.phi.getStateVector();

        if (stateVectorG.size() != stateVectorH.size()) {
            return false;
        }

        for (Map.Entry<String, Pair<Complex, String>> entryG : stateVectorG.entrySet()) {
            Pair<Complex, String> pairG = entryG.getValue();
            Pair<Complex, String> pairH = stateVectorH.get(entryG.getKey());

            if (pairH == null || !compareComplex(pairG.getKey(), pairH.getKey()) ) {
                return false;
            }
        }

        return Objects.equals(g.measurementResult, h.measurementResult); // Compare measurement results
    }

    /**
     * Helper function to compare complex numbers.
     * @param a Complex number A.
     * @param b Complex number B.
     * @return True if complex numbers A and B are equal, false otherwise.
     */
    private static boolean compareComplex(Complex a, Complex b) {
        return Double.compare(a.getReal(), b.getReal()) == 0;
    }
}
