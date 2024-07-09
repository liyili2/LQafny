package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.*;

public class DisQSimulation {
    static class Configuration {
        QuantumState1 phi;
        List<String> gates; // list of gate operations
        double probability;
        String measurementResult;

        Configuration(QuantumState1 phi, List<String> gates, double probability) {
            this.phi = phi;
            this.gates = gates;
            this.probability = probability;
            this.measurementResult = null; // Initialize measurement result as null
        }

        // Copy constructor for creating a new Configuration based on an existing one
        Configuration(Configuration config) {
            this.phi = new QuantumState1();
            this.phi.setStateVector(new HashMap<>(config.phi.getStateVector()));
            this.gates = new ArrayList<>(config.gates);
            this.probability = config.probability;
            this.measurementResult = config.measurementResult;
        }

        // Apply the gates to the quantum state
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

        void measureQubit(int qubitIndex) {
            measurementResult = phi.measureQubit(qubitIndex); // Store measurement result
        }

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

        @Override
        public int hashCode() {
            return Objects.hash(phi, gates, probability, measurementResult);
        }
    }

    public static void main(String[] args) {
        // Example setup of configurations G and H
        QuantumState1 stateG = new QuantumState1();
        QuantumState1 stateH = new QuantumState1();

        // Add initial qubits and gates for G and H
        stateG.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane", 0.5);
        stateG.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane", 0.5);
        stateG.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane", 0.5);

        stateH.addQubit(new Locus(0), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane", 0.5);
        stateH.addQubit(new Locus(1), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane", 0.5);
        stateH.addQubit(new Locus(2), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane", 0.5);

        stateG.printStateVector();
        stateH.printStateVector();

        Configuration configG = new Configuration(stateG, Arrays.asList("Hadamard", "CNot"), 0.5);
        Configuration configH = new Configuration(stateH, Arrays.asList("Hadamard", "CNot"), 0.5);

        // Apply gates
        configG.applyGates();
        configH.applyGates();

        // Measure qubits
        configG.measureQubit(2);
        configH.measureQubit(2);

        Set<Configuration> setG = new HashSet<>(Collections.singleton(configG));
        Set<Configuration> setH = new HashSet<>(Collections.singleton(configH));

        boolean result = notSim(setG, setH);

        System.out.println("Simulation result: " + result);
    }

    // Function to check simulation equivalence
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

            if (pairH == null || !compareComplex(pairG.getKey(), pairH.getKey()) || !pairG.getValue().equals(pairH.getValue())) {
                return false;
            }
        }

        return Objects.equals(g.measurementResult, h.measurementResult); // Compare measurement results
    }

    private static boolean compareComplex(Complex a, Complex b) {
        return Double.compare(a.getReal(), b.getReal()) == 0;
    }
}
