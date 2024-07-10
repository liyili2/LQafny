package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;

// A simple generic Pair class for handling tuples
class Pair<K, V> {
    private K key;
    private V value;

    public Pair(K key, V value) {
        this.key = key;
        this.value = value;
    }

    public K getKey() { return key; }
    public void setKey(K key) { this.key = key; }

    public V getValue() { return value; }
    public void setValue(V value) { this.value = value; }
}

// Class to define locations of qubits or groups of qubits
class Locus {
    private int[] indices;

    public Locus(int... indices) {
        this.indices = indices;
    }

    public int[] getIndices() { return indices; }
}

/**
 * Represents the quantum state of a system consisting of qubits.
 */
public class QuantumState1 {
    // State vectors with complex amplitudes and associated membrane labels
    private Map<String, Pair<Complex, String>> stateVectors = new HashMap<>();
    // Probabilities of measuring specific states
    private Map<String, Double> probabilities = new HashMap<>();
    // Probability associated with current state
    private double probability;
    // Norm of the state vector
    private double norm;


    

    /**
     * Adds a qubit to the quantum state with specified amplitude and probability.
     * @param locus The locus (location) of the qubit.
     * @param qubit The qubit to be added.
     * @param membraneLabel The label of the membrane where the qubit is located.
     * @param probability The probability associated with the state.
     */
    public void addQubit(Locus locus, Qubit qubit, String membraneLabel, double probability) {
        this.probability = probability;

        // Initialize state vectors if empty, otherwise combine existing state vectors with new qubit
        if (stateVectors.isEmpty()) {
            stateVectors.put("0", new Pair<>(qubit.getZeroAmplitude(), membraneLabel));
            stateVectors.put("1", new Pair<>(qubit.getOneAmplitude(), membraneLabel));
        } else {
            Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();
            stateVectors.forEach((key, value) -> {
                newStateVector.put(key + "0", new Pair<>(value.getKey().mul(qubit.getZeroAmplitude()), membraneLabel));
                newStateVector.put(key + "1", new Pair<>(value.getKey().mul(qubit.getOneAmplitude()), membraneLabel));
            });
            stateVectors = newStateVector;
        }
    }

    /**
     * Sets up an entangled Bell pair between two qubits at specified indices.
     * @param qubitIndex1 Index of the first qubit.
     * @param qubitIndex2 Index of the second qubit.
     */
    public void ENType(int qubitIndex1, int qubitIndex2) {
        stateVectors.clear();  // Clear existing state vectors to initialize new entanglement

        // Build binary keys for the new entangled states
        String key00 = "", key11 = "";
        int maxIndex = Math.max(qubitIndex1, qubitIndex2);
        for (int i = 0; i <= maxIndex; i++) {
            key00 += "0";
            key11 += "0";
        }
        char[] key00Array = key00.toCharArray();
        char[] key11Array = key11.toCharArray();
        key00Array[qubitIndex1] = '0';
        key00Array[qubitIndex2] = '0';
        key11Array[qubitIndex1] = '1';
        key11Array[qubitIndex2] = '1';

        key00 = new String(key00Array);
        key11 = new String(key11Array);

        // Add the Bell pair states to the state vectors with equal superposition
        stateVectors.put(key00, new Pair<>(new Complex(1.0 / Math.sqrt(2), 0), "Bell Pair"));
        stateVectors.put(key11, new Pair<>(new Complex(1.0 / Math.sqrt(2), 0), "Bell Pair"));

        normalizeStateVector();  // Normalize the state vectors if necessary
    }

    /**
     * Determines the most likely global quantum state based on the probabilities of state amplitudes.
     * @return A bit string representing the most likely quantum state.
     */
    public String NorType() {
        String mostProbableState = null;
        double maxProbability = 0;

        // Iterate through all state vectors to find the one with the highest probability
        for (Map.Entry<String, Pair<Complex, String>> entry : stateVectors.entrySet()) {
            double currentProbability = Math.pow(entry.getValue().getKey().getReal(), 2) + Math.pow(entry.getValue().getKey().getImag(), 2);
            if (currentProbability > maxProbability) {
                maxProbability = currentProbability;
                mostProbableState = entry.getKey();
            }
        }

        // Return the bit string of the most probable state
        return mostProbableState != null ? "|" + mostProbableState + ">" : "No state defined";
    }


    

    /**
     * Applies the Hadamard gate operation to a qubit at the specified index.
     * @param qubitIndex The index of the qubit.
     */
    public void applyHadamardToQubit(int qubitIndex) {
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();

        // Apply Hadamard gate to each state vector entry
        stateVectors.forEach((state, pair) -> {
            char bit = state.charAt(qubitIndex);
            String flippedBit = bit == '0' ? "1" : "0";

            String baseState0 = state.substring(0, qubitIndex) + "0" + state.substring(qubitIndex + 1);
            String baseState1 = state.substring(0, qubitIndex) + "1" + state.substring(qubitIndex + 1);

            Complex coeff = new Complex(0.7071067811865475, 0); // 1/sqrt(2)

            newStateVector.merge(baseState0, new Pair<>(pair.getKey().mul(coeff), pair.getValue()), (oldVal, newVal) -> new Pair<>(oldVal.getKey().add(newVal.getKey()), oldVal.getValue()));
            if (bit == '0') {
                newStateVector.merge(baseState1, new Pair<>(pair.getKey().mul(coeff), pair.getValue()), (oldVal, newVal) -> new Pair<>(oldVal.getKey().add(newVal.getKey()), oldVal.getValue()));
            } else {
                newStateVector.merge(baseState1, new Pair<>(pair.getKey().mul(coeff).negate(), pair.getValue()), (oldVal, newVal) -> new Pair<>(oldVal.getKey().add(newVal.getKey()), oldVal.getValue()));
            }
        });

        stateVectors = newStateVector;
        normalizeStateVector();
    }

    /**
     * Applies the Pauli-X (NOT) gate operation to a qubit at the specified index.
     * @param qubitIndex The index of the qubit.
     */
    public void applyXToQubit(int qubitIndex) {
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();

        // Apply Pauli-X gate to each state vector entry
        stateVectors.forEach((state, pair) -> {
            char bit = state.charAt(qubitIndex);
            String flippedState = state.substring(0, qubitIndex) + (bit == '0' ? "1" : "0") + state.substring(qubitIndex + 1);

            newStateVector.put(flippedState, pair);
        });

        stateVectors = newStateVector;
        normalizeStateVector();
    }

    /**
     * Applies the controlled Pauli-X (CNOT) gate operation between a control qubit and a target qubit.
     * @param controlQubitIndex The index of the control qubit.
     * @param targetQubitIndex The index of the target qubit.
     */
    public void applyControlledXToQubit(int controlQubitIndex, int targetQubitIndex) {
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();

        // Apply controlled Pauli-X gate to each state vector entry
        stateVectors.forEach((state, pair) -> {
            char controlBit = state.charAt(controlQubitIndex);
            if (controlBit == '1') {
                char targetBit = state.charAt(targetQubitIndex);
                String flippedState = state.substring(0, targetQubitIndex) + (targetBit == '0' ? "1" : "0") + state.substring(targetQubitIndex + 1);
                newStateVector.put(flippedState, pair);
            } else {
                newStateVector.put(state, pair);
            }
        });

        stateVectors = newStateVector;
        normalizeStateVector();
    }

    /**
     * Applies the rotation Z gate operation to a qubit at the specified index with the given angle.
     * @param qubitIndex The index of the qubit.
     * @param theta The angle of rotation.
     */
    public void applyRotationZToQubit(int qubitIndex, double theta) {
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();
        Complex phaseFactor = Complex.fromPolar(1, theta);

        // Apply rotation Z gate to each state vector entry
        stateVectors.forEach((state, pair) -> {
            char bit = state.charAt(qubitIndex);
            if (bit == '1') {
                newStateVector.put(state, new Pair<>(pair.getKey().mul(phaseFactor), pair.getValue()));
            } else {
                newStateVector.put(state, pair);
            }
        });

        stateVectors = newStateVector;
        normalizeStateVector();
    }

    /**
     * Applies the Quantum Fourier Transform (QFT) to the state.
     */
    public void applyQFT() {
        int n = (int) (Math.log(stateVectors.size()) / Math.log(2)); // Number of qubits

        // Apply Hadamard gate to each qubit and controlled rotation gates
        for (int i = 0; i < n; i++) {
            applyHadamardToQubit(i);
            for (int j = i + 1; j < n; j++) {
                double theta = Math.PI / Math.pow(2, j - i);
                applyControlledRotationZToQubit(i, j, theta);
            }
        }

        // Reverse the order of qubits (bitwise swap)
        for (int i = 0; i < n / 2; i++) {
            swapQubits(i, n - i - 1);
        }
    }

    /**
     * Applies a controlled rotation Z gate operation between a control qubit and a target qubit with the given angle.
     * @param controlQubitIndex The index of the control qubit.
     * @param targetQubitIndex The index of the target qubit.
     * @param theta The angle of rotation.
     */
    private void applyControlledRotationZToQubit(int controlQubitIndex, int targetQubitIndex, double theta) {
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();
        Complex phaseFactor = Complex.fromPolar(1, theta);

        // Apply controlled rotation Z gate to each state vector entry
        stateVectors.forEach((state, pair) -> {
            char controlBit = state.charAt(controlQubitIndex);
            if (controlBit == '1') {
                char targetBit = state.charAt(targetQubitIndex);
                if (targetBit == '1') {
                    newStateVector.put(state, new Pair<>(pair.getKey().mul(phaseFactor), pair.getValue()));
                } else {
                    newStateVector.put(state, pair);
                }
            } else {
                newStateVector.put(state, pair);
            }
        });

        stateVectors = newStateVector;
        normalizeStateVector();
    }

    /**
     * Swaps the qubits at the specified indices.
     * @param qubitIndex1 The index of the first qubit to swap.
     * @param qubitIndex2 The index of the second qubit to swap.
     */
    public void swapQubits(int qubitIndex1, int qubitIndex2) {
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();

        // Swap qubits in each state vector entry
        stateVectors.forEach((state, pair) -> {
            char[] newStateArray = state.toCharArray();
            char temp = newStateArray[qubitIndex1];
            newStateArray[qubitIndex1] = newStateArray[qubitIndex2];
            newStateArray[qubitIndex2] = temp;

            String newState = new String(newStateArray);
            newStateVector.put(newState, pair);
        });

        stateVectors = newStateVector;
    }

    /**
     * Simulates the quantum teleportation of a qubit to a target quantum state.
     * @param targetState The target quantum state where the qubit is teleported.
     * @param qubitIndex The index of the qubit to teleport.
     */
    public void teleportQubit(QuantumState1 targetState, int qubitIndex) {
        // Simulate quantum teleportation by copying the state to the target state
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>(targetState.getStateVector());
        this.stateVectors.forEach((state, pair) -> {
            if (state.charAt(qubitIndex) == '1') {
                String newState = state.substring(0, qubitIndex) + '1' + state.substring(qubitIndex + 1);
                newStateVector.merge(newState, new Pair<>(pair.getKey(), pair.getValue()), (oldVal, newVal) -> new Pair<>(oldVal.getKey().add(newVal.getKey()), newVal.getValue()));
            }
        });

        targetState.setStateVector(newStateVector);
        targetState.normalizeStateVector();
    }

    /**
     * Measures the qubit at the specified index and collapses the state to the measured outcome.
     * @param qubitIndex The index of the qubit to measure.
     * @return The measurement result ('0' or '1').
     */
    public String measureQubit(int qubitIndex) {
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();

        // Calculate probabilities of measuring '0' and '1'
        double zeroProbability = stateVectors.entrySet().stream()
            .filter(entry -> entry.getKey().charAt(qubitIndex) == '0')
            .mapToDouble(entry -> entry.getValue().getKey().abssqr())
            .sum();

        double oneProbability = 1.0 - zeroProbability;

        if (Math.abs(zeroProbability) < 1e-10 && Math.abs(oneProbability) < 1e-10) {
            System.out.println("Measurement error: probabilities are too close to zero.");
            return null;
        }

        probabilities.put("0", zeroProbability);
        probabilities.put("1", oneProbability);

        Random random = new Random();
        boolean measureZero = random.nextDouble() < zeroProbability;

        String measurementResult = measureZero ? "0" : "1";
        double normalizationFactor = measureZero ? Math.sqrt(zeroProbability) : Math.sqrt(oneProbability);

        // Update state vector according to measurement result
        stateVectors.forEach((state, pair) -> {
            if (state.charAt(qubitIndex) == measurementResult.charAt(0)) {
                String newState = state.substring(0, qubitIndex) + state.substring(qubitIndex + 1);
                newStateVector.merge(newState, new Pair<>(pair.getKey().div(normalizationFactor), pair.getValue()), (oldVal, newVal) -> new Pair<>(oldVal.getKey().add(newVal.getKey()), oldVal.getValue()));
            }
        });

        stateVectors = newStateVector;
        normalizeStateVector();

        System.out.println("Measurement result: " + measurementResult);
        return measurementResult;
    }

    /**
     * Normalizes the state vector to maintain quantum state probabilities.
     */
    public void normalizeStateVector() {
        // Calculate the norm of the state vector
        norm = stateVectors.values().stream()
                        .mapToDouble(pair -> pair.getKey().abssqr())
                        .sum();

        if (Math.abs(norm) < 1e-10) {
            System.out.println("Normalization error: Norm is zero or too close to zero.");
            return;
        }

        norm = Math.sqrt(norm);
        
        // Normalize the state vector
        stateVectors.replaceAll((key, value) -> new Pair<>(value.getKey().div(norm), value.getValue()));
    }

    /**
     * Prints the current quantum state vector.
     */
    public void printStateVector() {
        stateVectors.forEach((key, pair) -> {
            if (pair.getKey().getReal() != 0 || pair.getKey().getImag() != 0) {
                System.out.println("|" + key + "> = " + pair.getKey() + " (Membrane: " + pair.getValue() + ")");
            }
        });
    }

    /**
     * Prints the probabilities of measuring '0' and '1' for the current quantum state.
     */
    public void printProbabilities() {
        probabilities.forEach((key, value) -> {
            System.out.println("Probability of measuring " + key + ": " + value);
        });
    }

    /**
     * Prints the current quantum state vector with associated probabilities.
     */
    public void printStateVectorWithProbabilities() {
        stateVectors.forEach((key, pair) -> {
            if (pair.getKey().getReal() != 0 || pair.getKey().getImag() != 0) {
                System.out.println("|" + key + "> = " + pair.getKey() + " (Membrane: " + pair.getValue() + ") with Probability: " + probability);
            }
        });
    }

    // Getter for state vector
    public Map<String, Pair<Complex, String>> getStateVector() {
        return stateVectors;
    }

    // Setter for state vector
    public void setStateVector(Map<String, Pair<Complex, String>> stateVectors) {
        this.stateVectors = stateVectors;
    }

    public int getnumberofqubits()
    {
        return stateVectors.size();
    }
}
