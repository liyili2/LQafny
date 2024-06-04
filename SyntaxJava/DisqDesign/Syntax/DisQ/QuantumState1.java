package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.HashMap;
import java.util.Map;
import java.util.*;
import java.util.stream.Collectors;


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




public class QuantumState1 {
    private Map<String, Pair<Complex, String>> stateVectors = new HashMap<>();
    private Map<String, Double> probabilities = new HashMap<>();
    private double probability;
    double norm;

    public void addQubit(Locus locus, Qubit qubit, String membraneLabel, double probability) {
        this.probability = probability;
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

    public void applyHadamardToQubit(int qubitIndex) {
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();

        stateVectors.forEach((state, pair) -> {
            char bit = state.charAt(qubitIndex);
            String flippedBit = bit == '0' ? "1" : "0";

            String baseState0 = state.substring(0, qubitIndex) + "0" + state.substring(qubitIndex + 1);
            String baseState1 = state.substring(0, qubitIndex) + "1" + state.substring(qubitIndex + 1);

            Complex coeff = new Complex(0.7071067811865475, 0);

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

    public void applyRotationZToQubit(int qubitIndex, double theta) {
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();
        Complex phaseFactor = Complex.fromPolar(1, theta);

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

    public void measureQubit(int qubitIndex) {
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();
        double zeroProbability = stateVectors.entrySet().stream()
            .filter(entry -> entry.getKey().charAt(qubitIndex) == '0')
            .mapToDouble(entry -> entry.getValue().getKey().abssqr())
            .sum();

        double oneProbability = 1.0 - zeroProbability;

        if (Math.abs(zeroProbability) < 1e-10 && Math.abs(oneProbability) < 1e-10) {
            System.out.println("Measurement error: probabilities are too close to zero.");
            return;
        }

        probabilities.put("0", zeroProbability);
        probabilities.put("1", oneProbability);

        Random random = new Random();
        boolean measureZero = random.nextDouble() < zeroProbability;

        String measurementResult = measureZero ? "0" : "1";
        double normalizationFactor = measureZero ? Math.sqrt(zeroProbability) : Math.sqrt(oneProbability);

        stateVectors.forEach((state, pair) -> {
            if (state.charAt(qubitIndex) == measurementResult.charAt(0)) {
                String newState = state.substring(0, qubitIndex) + state.substring(qubitIndex + 1);
                newStateVector.merge(newState, new Pair<>(pair.getKey().div(normalizationFactor), pair.getValue()), (oldVal, newVal) -> new Pair<>(oldVal.getKey().add(newVal.getKey()), oldVal.getValue()));
            }
        });

        stateVectors = newStateVector;
        normalizeStateVector();

        System.out.println("Measurement result: " + measurementResult);
    }

    public void normalizeStateVector() {
         norm = stateVectors.values().stream()
                        .mapToDouble(pair -> pair.getKey().abssqr())
                        .sum();

        if (Math.abs(norm) < 1e-10) {
            System.out.println("Normalization error: Norm is zero or too close to zero.");
            return;
        }

        norm = Math.sqrt(norm);
        stateVectors.replaceAll((key, value) -> new Pair<>(value.getKey().div(norm), value.getValue()));
    }

    public void printStateVector() {
        stateVectors.forEach((key, pair) -> {
            if (pair.getKey().getReal() != 0 || pair.getKey().getImag() != 0) {
                System.out.println("|" + key + "> = " + pair.getKey() + " (Membrane: " + pair.getValue() + ")");
            }
        });
    }

    public void printProbabilities() {
        probabilities.forEach((key, value) -> {
            System.out.println("Probability of measuring " + key + ": " + value);
        });
    }

    public void printStateVectorWithProbabilities() {
        stateVectors.forEach((key, pair) -> {
            if (pair.getKey().getReal() != 0 || pair.getKey().getImag() != 0) {
                System.out.println("|" + key + "> = " + pair.getKey() + " (Membrane: " + pair.getValue() + ") with Probability: " + probability);
            }
        });
    }

     // Getter for stateVector
     public Map<String, Pair<Complex, String>> getStateVector() {
        return stateVectors;
    }

    // Setter for stateVector
    public void setStateVector(Map<String, Pair<Complex, String>> stateVectors) {
        this.stateVectors = stateVectors;
    }
}
