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
        QuantumState1 phi;  // Quantum state
        List<String> gates;  // List of gate operations
        double probability;  // Accumulated probability
        String measurementResult;  // Measurement result

        Configuration(QuantumState1 phi, List<String> gates, double probability) {
            this.phi = phi;
            this.gates = gates;
            this.probability = probability;
            this.measurementResult = null; // Initialize measurement result as null
        }

        void applyGates() {
            for (String gate : gates) {
                switch (gate) {
                    case "Hadamard":
                        phi.applyHadamardToQubit(0);
                        break;
                    case "CNot":
                        phi.applyControlledXToQubit(0, 1);
                        break;
                    // Add additional gates if needed
                }
            }
        }

        void measureQubit(int qubitIndex) {
            measurementResult = phi.measureQubit(qubitIndex);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Configuration that = (Configuration) o;
            return Double.compare(that.probability, probability) == 0 &&
                    Objects.equals(phi, that.phi) &&
                    Objects.equals(gates, that.gates) &&
                    Objects.equals(measurementResult, that.measurementResult);
        }

        @Override
        public int hashCode() {
            return Objects.hash(phi, gates, probability, measurementResult);
        }
    }

    /**
     * Method for checking equivalence between sequential and distributed systems using DisQ observable simulation.
     * @param sequential Set of configurations for the sequential system.
     * @param distributed Set of configurations for the distributed system.
     * @return True if systems are not equivalent, false otherwise.
     */
    public static boolean notSim(Set<Configuration> sequential, Set<Configuration> distributed) {
        for (Configuration configSeq : sequential) {
            boolean matchFound = false;
            for (Configuration configDist : distributed) {
                if (transitionsMatch(configSeq, configDist)) {
                    matchFound = true;
                    break;
                }
            }
            if (!matchFound) {
                return true;  // No matching configuration found in distributed system for a sequential configuration
            }
        }
        return false;
    }

    /**
     * Helper function to compare transitions between two configurations.
     * @param g Configuration for sequential system.
     * @param h Configuration for distributed system.
     * @return True if transitions match, false otherwise.
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

            if (pairH == null || !compareComplex(pairG.getKey(), pairH.getKey())) {
                return false;
            }
        }

        return Objects.equals(g.measurementResult, h.measurementResult);
    }

    /**
     * Helper function to compare complex numbers.
     * @param a Complex number A.
     * @param b Complex number B.
     * @return True if complex numbers are equal, false otherwise.
     */
    private static boolean compareComplex(Complex a, Complex b) {
        return Double.compare(a.getReal(), b.getReal()) == 0 && Double.compare(a.getImag(), b.getImag()) == 0;
    }

    public static void main(String[] args) {
        // Setup for Sequential System (G)
        QuantumState1 sequentialState = new QuantumState1();
        sequentialState.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membraneSeq", 1);
        sequentialState.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membraneSeq", 1);
        
        Configuration configSeq = new Configuration(sequentialState, Arrays.asList("Hadamard", "CNot"), 0.5);
        configSeq.applyGates();
        configSeq.measureQubit(0);
        
        Set<Configuration> setSequential = new HashSet<>(Collections.singleton(configSeq));
        
        // Setup for Distributed System (H)
        QuantumState1 distributedState = new QuantumState1();
        distributedState.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 1);
        distributedState.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane2", 1);
        
        Configuration configDist = new Configuration(distributedState, Arrays.asList("Hadamard", "CNot"), 0.5);
        configDist.applyGates();
        configDist.measureQubit(1);
        
        Set<Configuration> setDistributed = new HashSet<>(Collections.singleton(configDist));
        
        // Check if sequential and distributed systems are not simulation equivalent
        boolean result = notSim(setSequential, setDistributed);
        System.out.println("Sequential and Distributed systems are not equivalent: " + result);
    }
}
