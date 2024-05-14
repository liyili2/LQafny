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
    private Complex amplitude;
    private double phase;

    public EntangledState(Complex amplitude, double phase) {
        this.amplitude = amplitude;
        this.phase = phase;
    }

    public Complex getAmplitude() { return amplitude; }
    public void setAmplitude(Complex amplitude) { this.amplitude = amplitude; }

    public double getPhase() { return phase; }
    public void setPhase(double phase) { this.phase = phase; }
}

// Primary class for managing the quantum state
/**public class QuantumState {
    private List<Pair<Locus, EntangledState>> statePairs;
    //private Random random = new Random();

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
           // if (matchIndices(pair.getKey().getIndices(), targetIndices)) 
            {
                double amplitude = pair.getValue().getAmplitude();
                double phase = pair.getValue().getPhase();
              //  System.err.println("Hello testing\n");
                
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
    /**public int measure(int c, int N, int p) {
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
        int result = pickRandomBasedOnProbability(withPrefixC, totalProbability, N,c);
    
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
        return -1; // something went wrong with the probability calculations
    }***/

//} 

public class QuantumState {
    private List<Pair<Locus, EntangledState>> entangledStates;
    public List<QuantumValue> quantumValues;  // To hold all quantum states
    List<Pair<Locus, Qubit>> qubits;

    public QuantumState() {
        this.qubits = new ArrayList<>();
    }

    public void addQubit(Locus locus, Qubit qubit) {
        qubits.add(new Pair<>(locus, qubit));
    }

    /**public QuantumState() {
        this.quantumValues = new ArrayList<>();
    }**/

    
    /**ublic QuantumState() {
        entangledStates = new ArrayList<>();
    }**/

    public void addEntangledState(Locus locus, EntangledState state) {
        entangledStates.add(new Pair<>(locus, state));
    }

   /**  public void applyHadamard(int[] targetIndices) {
        entangledStates.stream()
            .filter(pair -> matchIndices(pair.getKey().getIndices(), targetIndices))
            .forEach(pair -> {
                Complex amplitude = pair.getValue().getAmplitude();
                double phase = pair.getValue().getPhase();
                pair.getValue().setAmplitude(amplitude.mul(new Complex(Math.sqrt(0.5), Math.sqrt(0.5))));
                pair.getValue().setPhase(phase + Math.PI / 2);  // Example phase manipulation
            });
    }**/
    public void applyHadamard(int qubitIndex, QuantumValue quantumValue) {
        int numStates = quantumValue.getAmplitudes().length;
        Complex[] newAmplitudes = new Complex[numStates];
    
        // Initialize new amplitude array
        for (int i = 0; i < numStates; i++) {
            newAmplitudes[i] = new Complex(0, 0);
        }
    
        // Apply the Hadamard transformation
        for (int i = 0; i < numStates; i++) {
            int indexWithFlippedQubit = i ^ (1 << qubitIndex); // Flip the qubit at qubitIndex
    
            // Calculate new amplitudes
            Complex currentAmplitude = quantumValue.getAmplitude(i);
            Complex currentAmplitudeFlipped = quantumValue.getAmplitude(indexWithFlippedQubit);
    
            // Superposition: |0> + |1> and |0> - |1>
            newAmplitudes[i] = currentAmplitude.add(currentAmplitudeFlipped).mul(1/Math.sqrt(2));
            newAmplitudes[indexWithFlippedQubit] = currentAmplitude.sub(currentAmplitudeFlipped).mul(1/Math.sqrt(2));
        }
    
        // Set the new amplitudes back to the quantum value
        for (int i = 0; i < numStates; i++) {
            quantumValue.setAmplitude(i, newAmplitudes[i]);
        }
    }
    

    private boolean matchIndices(int[] indices1, int[] indices2) {
        if (indices1.length != indices2.length) return false;
        for (int i = 0; i < indices1.length; i++) {
            if (indices1[i] != indices2[i]) return false;
        }
        return true;
    }

    public Complex measure(Locus locus) {
        // Measurement collapses the quantum state to one of the eigenstates
        // Assuming a simple measurement that just returns the amplitude without collapse for demonstration
        return entangledStates.stream()
                .filter(pair -> matchIndices(pair.getKey().getIndices(), locus.getIndices()))
                .findFirst()
                .map(pair -> pair.getValue().getAmplitude())
                .orElse(Complex.ZERO);
    }

    public void applyCNOT(int controlIndex, int targetIndex) {
        // Iterate over all possible states (amplitudes)
        for (int i = 0; i < quantumValues.size(); i++) {
            QuantumValue qv = quantumValues.get(i);
            Complex[] newAmplitudes = new Complex[qv.amplitudes.length];
            System.arraycopy(qv.amplitudes, 0, newAmplitudes, 0, qv.amplitudes.length);
    
            // Perform the CNOT operation
            for (int state = 0; state < newAmplitudes.length; state++) {
                if ((state & (1 << controlIndex)) != 0) { // Control qubit is |1>
                    int targetState = state ^ (1 << targetIndex); // Flip the target qubit
                    newAmplitudes[targetState] = qv.getAmplitude(state);
                    newAmplitudes[state] = qv.getAmplitude(targetState);
                }
            }
            qv.amplitudes = newAmplitudes; // Update the state with new amplitudes
        }
    }
    

    public void initializeQubits(int numQubits) {
        Complex[] amplitudes = new Complex[1 << numQubits]; // 2^numQubits amplitudes
        Random random = new Random();
        for (int i = 0; i < amplitudes.length; i++) {
            float real = random.nextFloat();
            float imag = random.nextFloat();
            amplitudes[i] = new Complex(real, imag);
        }
        QuantumValue qv = new QuantumValue(amplitudes);
        qv.normalize();  // Normalize to ensure the total probability amplitude is 1
        this.quantumValues.add(qv);
    }

    public void printState() {
        for (QuantumValue qv : quantumValues) {
            for (int i = 0; i < qv.amplitudes.length; i++) {
                System.out.println("State |" + Integer.toBinaryString(i) + "> Amplitude: " + qv.getAmplitude(i));
            }
        }
    }
    // Example method to print all qubits
    public void printQubits() {
        for (Pair<Locus, Qubit> pair : qubits) {
            System.out.println("Locus: " + pair.getKey() + " Qubit states: |0> " + pair.getValue().getZeroAmplitude() + ", |1> " + pair.getValue().getOneAmplitude());
        }
    }

    public void applyHadamardToQubit(int qubitIndex) {
        if (qubitIndex < 0 || qubitIndex >= qubits.size()) {
            System.out.println("Invalid qubit index.");
            return;
        }
        Pair<Locus, Qubit> pair = qubits.get(qubitIndex);
        Qubit qubit = pair.getValue();
        Complex newZeroAmplitude = qubit.getZeroAmplitude().add(qubit.getOneAmplitude()).mul(new Complex(1 / Math.sqrt(2), 0));
        Complex newOneAmplitude = qubit.getZeroAmplitude().sub(qubit.getOneAmplitude()).mul(new Complex(1 / Math.sqrt(2), 0));
        qubit.setZeroAmplitude(newZeroAmplitude);
        qubit.setOneAmplitude(newOneAmplitude);
    }
    

}



    


