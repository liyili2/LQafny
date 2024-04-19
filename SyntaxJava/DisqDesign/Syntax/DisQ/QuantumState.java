package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.ArrayList;
import java.util.List;
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

// Class to represent an entangled quantum state
class EntangledState {
    private double amplitude;
    private double phase;

    public EntangledState(double amplitude, double phase) {
        this.amplitude = amplitude;
        this.phase = phase;
    }

    public double getAmplitude() { return amplitude; }
    public void setAmplitude(double amplitude) { this.amplitude = amplitude; }

    public double getPhase() { return phase; }
    public void setPhase(double phase) { this.phase = phase; }
}

// Primary class for managing the quantum state
class QuantumState {
    private List<Pair<Locus, EntangledState>> statePairs;
    private Random random = new Random();

    public QuantumState() {
        statePairs = new ArrayList<>();
    }

    public void addStatePair(Locus locus, EntangledState state) {
        statePairs.add(new Pair<>(locus, state));
    }

   
    public void applyHadamard(int[] targetIndices) {
        for (Pair<Locus, EntangledState> pair : statePairs) {
            if (matchIndices(pair.getKey().getIndices(), targetIndices)) {
                double amplitude = pair.getValue().getAmplitude();
                double phase = pair.getValue().getPhase();
                
                pair.getValue().setAmplitude(Math.sqrt(0.5) * (amplitude + phase));
                pair.getValue().setPhase(Math.sqrt(0.5) * (amplitude - phase));
            }
        }
    }

    private boolean matchIndices(int[] indices, int[] targetIndices) {
        if (indices.length != targetIndices.length) return false;
        for (int i = 0; i < indices.length; i++) {
            if (indices[i] != targetIndices[i]) return false;
        }
        return true;
    }

    public String measure(int[] targetIndices) {
        StringBuilder result = new StringBuilder();
        for (int index : targetIndices) {
            for (Pair<Locus, EntangledState> pair : statePairs) {
                if (pair.getKey().getIndices()[0] == index) {
                    
                    double probabilityOfOne = Math.pow(pair.getValue().getAmplitude(), 2);
                    boolean isOne = random.nextDouble() < probabilityOfOne;
                    result.append(isOne ? "1" : "0");
                    break;
                }
            }
        }
        return result.toString();
    }
}

    


