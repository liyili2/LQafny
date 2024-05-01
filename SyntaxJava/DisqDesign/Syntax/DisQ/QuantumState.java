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
public class QuantumState {
    private List<Pair<Locus, EntangledState>> statePairs;
    private Random random = new Random();

    private List<QuantumValue> quantumValues; // Your quantum system's state representation

    public QuantumState(List<QuantumValue> quantumValues) {
        this.quantumValues = quantumValues;
    }

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
    public int measure(int c, int N, int p) {
        List<QuantumValue> withPrefixC = new ArrayList<>();
        for (QuantumValue qValue : quantumValues) {
            if (qValue.hasPrefix(c)) {
                withPrefixC.add(qValue);
            }
        }
    
        // Normalize the amplitudes of the remaining basis-kets
        withPrefixC.forEach(QuantumValue::normalize);
    
        // Calculate the sum of the squares of the magnitudes of the amplitudes (total probability)
        double totalProbability = withPrefixC.stream()
            .mapToDouble(qv -> qv.getMagnitudeSquared(c))
            .sum();
    
        // Probability of picking a basis value 'a mod N' as a measurement result
        int result = pickRandomBasedOnProbability(withPrefixC, totalProbability, N,int c);
    
        // Collapse the quantum state based on the result
        quantumValues.forEach(qv -> qv.collapse(result));
    
        return result;
    }
    
    private int pickRandomBasedOnProbability(List<QuantumValue> withPrefixC, double totalProbability, int N,int c) {
        double rand = Math.random() * totalProbability;
        double cumulativeProbability = 0.0;
    
        for (QuantumValue qv : withPrefixC) {
            double probability = qv.getMagnitudeSquared(c); // Assuming getMagnitudeSquared returns a double
            cumulativeProbability += probability;
            if (cumulativeProbability >= rand) {
                return qv.getBasisValue() % N;
            }
        }
        return -1;  // This means something went wrong with the probability calculations
    }
    


    /***
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
    }  ***/


     // Conceptual implementation of the quantum measurement described
   /** * public int measure(int c, int N, int p) {
        // Partitioning the basis-kets by the presence of c as prefix
        List<QuantumValue> withPrefixC = new ArrayList<>();
        List<QuantumValue> withoutPrefixC = new ArrayList<>();

        for (QuantumValue qValue : quantumValues) {
            if (qValue.hasPrefix(c)) {
                withPrefixC.add(qValue);
            } else {
                withoutPrefixC.add(qValue);
            }
        }

        // Normalize the amplitudes of the remaining basis-kets
       // double sumOfSquares = withPrefixC.stream().mapToDouble(QuantumValue::getMagnitudeSquared).sum();
       // double sumOfSquares = quantumValues.stream()
    //.mapToDouble(qv -> qv.getMagnitudeSquared(c)) // Make sure to pass an index if needed
   // .sum();

        //double normalizationFactor = 1 / Math.sqrt(sumOfSquares);
        withPrefixC.forEach(qv -> qv.normalize());
        

        // Calculate the sum of the amplitudes of the basis-kets (post-normalization)
        Complex amplitudeSum = ((QuantumValue) quantumValues).getAmplitude(c);
       // double amplitudeSum = withPrefixC.stream().mapToDouble(QuantumValue::getAmplitude).sum();
        
        // Probability of picking a basis value 'a mod N' as a measurement result
        int result = pickRandomBasedOnProbability(withPrefixC, amplitudeSum, N,c);
        
        // The number r of remaining basis-kets in range y[0,n) is computed by rounding 2^n/p
        int remainingBasisKets = (int)Math.round(Math.pow(2, N) / p);
        
        // Collapse the quantum state based on the result
        quantumValues.forEach(qv -> qv.collapse(result));
        
        return result;
    }

    private int pickRandomBasedOnProbability(List<QuantumValue> withPrefixC, Complex amplitudeSum, int N,int c) {
        double rand = Math.random() * amplitudeSum;
        double cumulativeProbability = 0.0;

        for (QuantumValue qv : withPrefixC) {
            cumulativeProbability += qv.getAmplitude(c);
            if (cumulativeProbability >= rand) {
                return qv.getBasisValue() % N;
            }
        }
        return -1; // This means something went wrong with the probability calculations
    }***/

}


    


