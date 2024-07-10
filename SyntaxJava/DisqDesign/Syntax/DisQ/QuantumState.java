package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.HashMap;
import java.util.Map;


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




public class QuantumState {
   // private List<Pair<Locus, EntangledState>> entangledStates;
    public List<QuantumValue> quantumValues;  // To hold all quantum states
    List<Pair<Locus, Qubit>> qubits;
    double norms;
    private double probability;  // Probability associated with the state

    

    public QuantumState() {
        this.qubits = new ArrayList<>();
    }
    private Map<String, Complex> stateVector = new HashMap<>();
    private Map<String, Pair<Complex, String>> stateVectors = new HashMap<>();
    private Map<String, Double> probabilities = new HashMap<>();
   

    public void SaddQubit(Locus locus, Qubit qubit) {
        if (stateVector.isEmpty()) {
            stateVector.put("0", qubit.getZeroAmplitude());
            stateVector.put("1", qubit.getOneAmplitude());
        } else {
            Map<String, Complex> newStateVector = new HashMap<>();
            // Tensor each existing state with the new qubit state
            stateVector.forEach((key, value) -> {
                newStateVector.put(key + "0", value.mul(qubit.getZeroAmplitude()));
                newStateVector.put(key + "1", value.mul(qubit.getOneAmplitude()));
            });
            stateVector = newStateVector;
        }
    }

    public void SaddQubit(Locus locus, Qubit qubit, String membraneLabel, double probability) {
        this.probability = probability;
        if (stateVectors.isEmpty()) {
            stateVectors.put("0", new Pair<>(qubit.getZeroAmplitude(), membraneLabel));
            stateVectors.put("1", new Pair<>(qubit.getOneAmplitude(), membraneLabel));
        } else {
            Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();
            // Tensor each existing state with the new qubit state
            stateVectors.forEach((key, value) -> {
                newStateVector.put(key + "0", new Pair<>(value.getKey().mul(qubit.getZeroAmplitude()), membraneLabel));
                newStateVector.put(key + "1", new Pair<>(value.getKey().mul(qubit.getOneAmplitude()), membraneLabel));
            });
            stateVectors = newStateVector;
        }
    }

    public void normalizeStateVector() {
          norms = stateVector.values().stream()
                         .mapToDouble(Complex::abssqr)
                         .sum();
        norms = Math.sqrt(norms);
        stateVector.forEach((key, value) -> stateVector.put(key, value.div(norms)));
    }

    public void printStateVector() {
        stateVector.forEach((key, value) -> 
            System.out.println("|" + key + "> = " + value));
    }

    public void applyHadamardToQubit(Locus locus) {
        // This is a conceptual method. Actual implementation will depend on quantum gate mathematics.
        // Typically, it would iterate through the stateVector and adjust amplitudes according to the Hadamard gate's effect.
        Map<String, Complex> newStateVector = new HashMap<>();
        stateVector.forEach((state, amplitude) -> {
            int index = locus.getIndices()[0];  // Assuming Locus holds indices of qubits
            String newState = state.substring(0, index) + 
                              (state.charAt(index) == '0' ? "1" : "0") + 
                              state.substring(index + 1);
            // Calculate new amplitudes based on Hadamard transformation rules
            Complex newAmplitude = amplitude.mul(new Complex(1 / Math.sqrt(2), 0)); // Simplified example
            newStateVector.put(state, newAmplitude);
            newStateVector.put(newState, newAmplitude);
        });
        stateVector = newStateVector;
        normalizeStateVector(); // Normalize after modification
    }
    


    public void addQubit(Locus locus, Qubit qubit) {
        qubit.normalize();
        qubits.add(new Pair<>(locus, qubit));
        //NEED TO NORMALIZE WHEN ADDING THE QUBIT
    }

    public int getnumberofqubits()
    {
        return qubits.size();
    }

   

    // Method to determine the NOR type based on the states of all qubits
    public String NorType() {
        StringBuilder result = new StringBuilder();
        result.append("|");
        for (Pair<Locus, Qubit> pair : qubits) {
            Qubit qubit = pair.getValue();
            double zeroProb = qubit.getZeroAmplitude().abssqr();
            double oneProb = qubit.getOneAmplitude().abssqr();

            if (zeroProb > oneProb) {
                result.append("0");  // More likely in state |0>
            } else {
                result.append("1");  // More likely in state |1>
            }
        }
        result.append(">");
        return result.toString();
    }
    //Initializing the entangle bits.
    public void ENType (int qubitindex1,int qubitindex2)

    {
        Pair<Locus, Qubit> qubit1 = qubits.get(qubitindex1);
        Pair<Locus, Qubit> qubit2 = qubits.get(qubitindex2);
        //qubit1 
	    qubit1.getValue().setOneAmplitude(new Complex(0.707, 0));
        qubit1.getValue().setZeroAmplitude(new Complex(0.707, 0));
        qubit1.getValue().setEN(true, qubitindex2);
        //qubit2 
        qubit2.getValue().setOneAmplitude(new Complex(0.707, 0));
        qubit2.getValue().setZeroAmplitude(new Complex(0.707, 0));
        qubit2.getValue().setEN(true, qubitindex1);


        
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

   
    // Example method to print all qubits
    public void printQubits() {
        for (Pair<Locus, Qubit> pair : qubits) {
            System.out.println("Locus: " + pair.getKey() + " Qubit states: |0> " + pair.getValue().getZeroAmplitude() + ", |1> " + pair.getValue().getOneAmplitude());
            //System.out.println("\n");
        }
        System.out.println("\n");
    }

    public void applyHadamardToQubit(int qubitIndex) {
        Map<String, Complex> newStateVector = new HashMap<>();
    
        // Update each state in the superposition
        stateVector.forEach((state, amplitude) -> {
            // Create states for the superposition
            String baseState0 = state.substring(0, qubitIndex) + "0" + state.substring(qubitIndex + 1);
            String baseState1 = state.substring(0, qubitIndex) + "1" + state.substring(qubitIndex + 1);
    
            // Hadamard on |0>
            Complex additionAmplitude = amplitude.mul(new Complex(0.7071067811865475, 0)); // 1/√2
            newStateVector.put(baseState0, newStateVector.getOrDefault(baseState0, new Complex(0, 0)).add(additionAmplitude));
            newStateVector.put(baseState1, newStateVector.getOrDefault(baseState1, new Complex(0, 0)).add(additionAmplitude));
    
            // Hadamard on |1>
            System.out.println("state.charAt(qubitIndex)=="+state.charAt(qubitIndex));
            if (state.charAt(qubitIndex) == '1') {
                newStateVector.put(baseState0, newStateVector.getOrDefault(baseState0, new Complex(0, 0)).add(additionAmplitude));
                newStateVector.put(baseState1, newStateVector.getOrDefault(baseState1, new Complex(0, 0)).add(additionAmplitude));
            }
        });
    
        stateVector = newStateVector;
        TnormalizeStateVector();
    }
    
    public void TnormalizeStateVector() {
        norms = stateVector.values().stream()
                        .mapToDouble(Complex::abssqr)
                        .sum();
    
        if (norms == 0) {
            System.out.println("Normalization error: Norm is zero.");
            return; // Avoid division by zero
        }
    
        norms = Math.sqrt(norms);
        stateVector.forEach((key, value) -> stateVector.put(key, value.div(norms)));
    }
    
    // public void applyHadamardToQubit(int qubitIndex) {
    //     if (qubitIndex < 0 || qubitIndex >= qubits.size()) {
    //         System.out.println("Invalid qubit index.");
    //         return;
    //     }
    
    //     // Calculate the new states
    //     int totalQubits = qubits.size();
    //     int numStates = 1 << totalQubits; // 2^totalQubits, total possible states
    //     Complex[] newStates = new Complex[numStates];
    
    //     // Initialize new states array
    //     Arrays.fill(newStates, new Complex(0, 0));
    
    //     // Update the state vector considering the Hadamard on the specified qubit
    //     for (int i = 0; i < numStates; i++) {
    //         // Calculate the index that flips the bit at the qubitIndex
    //         int indexWithFlip = i ^ (1 << qubitIndex);
    
    //         // Get the current amplitude
    //         Complex currentAmplitude = quantumValues[i];
    
    //         // Superpose the current and flipped state
    //         newStates[i] = newStates[i].add(currentAmplitude.mul(new Complex(1/Math.sqrt(2), 0)));
    //         newStates[indexWithFlip] = newStates[indexWithFlip].add(currentAmplitude.mul(new Complex(1/Math.sqrt(2), 0)));
    //     }
    
    //     // Replace old state vector with the new one
    //     for (int i = 0; i < numStates; i++) {
    //         quantumValues[i] = newStates[i];
    //     }
    // }
    
    public void CapplyHadamardToQubit(int qubitIndex) {
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

    // public void applyXgate (int qubitIndex)
    // {
    //     if (qubitIndex < 0 || qubitIndex >= qubits.size()) {
    //         System.out.println("Invalid qubit index.");
    //         return;
    //     }
    //     Pair<Locus, Qubit> pair = qubits.get(qubitIndex);
    //     Qubit qubit = pair.getValue();
    //     Complex temp = qubit.zeroAmplitude;
    //     qubit.zeroAmplitude = qubit.oneAmplitude;
    //     qubit.oneAmplitude = temp;

    // }
    public void applyXgate(int qubitIndex) {
        Map<String, Complex> newStateVector = new HashMap<>();
    
        // Iterate over each state in the existing state vector
        stateVector.forEach((state, amplitude) -> {
            // Determine the new state by flipping the specified qubit
            char[] stateChars = state.toCharArray();
            stateChars[qubitIndex] = stateChars[qubitIndex] == '0' ? '1' : '0';
            String newState = new String(stateChars);
    
            // Place the amplitude under the flipped state
            newStateVector.put(newState, amplitude);
        });
    
        // Replace the old state vector with the new state vector
        stateVector = newStateVector;
    }
    // public void applyControlXgate (int control, int target)
    // {
    //     if ((control < 0 && target < 0)|| (control >= qubits.size() && target >= qubits.size())) {
    //         System.out.println("Invalid qubit index.");
    //         return;
    //     }
    //     Pair<Locus, Qubit> cqubit = qubits.get(control);
    //     Pair<Locus,Qubit> tqubit = qubits.get(target);

    //     Qubit controlqubit = cqubit.getValue();
    //     Qubit targetqubit = tqubit.getValue();

    //     if (controlqubit.oneAmplitude.r> 0)
    //     {
    //     Complex temp = targetqubit.zeroAmplitude;
    //     targetqubit.zeroAmplitude = targetqubit.oneAmplitude;
    //     targetqubit.oneAmplitude = temp;
    //     }

    // }
    public void applyControlXgate(int control, int target) {
        Map<String, Complex> newStateVector = new HashMap<>();
    
        // Iterate over each state in the existing state vector
        stateVector.forEach((state, amplitude) -> {
            char[] stateChars = state.toCharArray();
            
            // Only flip the target qubit if the control qubit is in the |1> state
            if (stateChars[control] == '1') {
                stateChars[target] = stateChars[target] == '0' ? '1' : '0';
            }
            String newState = new String(stateChars);
    
            // Assign the amplitude to the possibly modified state
            newStateVector.put(newState, amplitude);
        });
    
        // Replace the old state vector with the new state vector
        stateVector = newStateVector;
    }
    

    // public void applyRzToQubit(int qubitIndex, double theta) {
    //     if (qubitIndex < 0 || qubitIndex >= qubits.size()) {
    //         System.out.println("Invalid qubit index.");
    //         return;
    //     }
    //     Pair<Locus, Qubit> pair = qubits.get(qubitIndex);
    //     Qubit qubit = pair.getValue();
    
    //     // Apply phase shift to the |1> amplitude
    //     Complex phaseFactor = Complex.fromPolar(1, theta); // Creating a complex number with magnitude 1 and phase theta
    //     Complex newOneAmplitude = qubit.getOneAmplitude().mul(phaseFactor);
    
    //     // Set the new amplitude for |1>
    //     qubit.setOneAmplitude(newOneAmplitude);
    // }

    public void applyRzToQubit(int qubitIndex, double theta) {
        Complex phaseFactor = Complex.fromPolar(1, theta); // Creating a complex number with magnitude 1 and phase theta
    
        // Update state vector for each computational basis state where the qubit is in the |1> state
        Map<String, Complex> newStateVector = new HashMap<>();
        stateVector.forEach((key, value) -> {
            // Only apply the phase shift if the qubit at qubitIndex is in the |1> state
            if (key.charAt(qubitIndex) == '1') {
                newStateVector.put(key, value.mul(phaseFactor));
            } else {
                newStateVector.put(key, value);
            }
        });
    
        stateVector = newStateVector;
        TnormalizeStateVector(); // It's a good practice to normalize the state vector if needed
    }

     // Method to apply the Quantum Fourier Transform
     public void applyQFT(int n) {
        for (int i = 0; i < n; i++) {
            applyHadamardToQubit3(i);
            for (int j = 1; j < n - i; j++) {
                applyControlledRotation(i, i + j, Math.PI / Math.pow(2, j));
            }
        }
        reverseQubits(n);
    }
    // Applying a controlled rotation gate
    private void applyControlledRotation(int control, int target, double theta) {
        stateVector.forEach((key, value) -> {
            if (key.charAt(control) == '1') {
                String newKey = key.substring(0, target) + "1" + key.substring(target + 1);
                Complex rotation = Complex.fromPolar(1, theta);
                stateVector.put(newKey, stateVector.get(newKey).mul(rotation));
            }
        });
    }

    // Method to reverse qubits after QFT
    private void reverseQubits(int n) {
        Map<String, Complex> newStateVector = new HashMap<>();
        stateVector.forEach((key, value) -> {
            String newKey = new StringBuilder(key).reverse().toString();
            newStateVector.put(newKey, value);
        });
        stateVector = newStateVector;
    }

    public Complex[] tensorProduct() {
        if (qubits.isEmpty()) {
            return new Complex[] {};  // Return an empty array if no qubits are present
        }

        // Start with the first qubit's state vector
        Complex[] result = { qubits.get(0).getValue().getZeroAmplitude(), qubits.get(0).getValue().getOneAmplitude() };

        // Apply the tensor product iteratively
        for (int i = 1; i < qubits.size(); i++) {
            Qubit qubit = qubits.get(i).getValue();
            Complex[] tempResult = new Complex[result.length * 2]; // Each new qubit doubles the state vector size

            // Compute the tensor product of result with the current qubit's state vector
            for (int j = 0; j < result.length; j++) {
                tempResult[2 * j] = result[j].mul(qubit.getZeroAmplitude());
                tempResult[2 * j + 1] = result[j].mul(qubit.getOneAmplitude());
            }

            result = tempResult; // Update the result to the newly computed tensor product
        }

        return result;
    }

    public void tensornorm()
    {
        Complex[] tensor = tensorProduct();
        double square=0.0, normsq=0.0;
        for (int i =0 ; i < tensor.length;i++)
        {
            square += tensor[i].abssqr();
            System.out.println(tensor[i].abssqr());
            
        }
        System.out.println("\nNomr:\n"+square);
        for (int i =0 ; i < tensor.length;i++)
        {
           tensor[i] = tensor[i].div(square);
            
        }
        for (int i =0 ; i < tensor.length;i++)
        {
            normsq += tensor[i].abssqr();
            
        }
        System.out.println("\nnormsq:\n"+normsq);
        
    }

    public void lprintTensorProduct() {
        Complex[] tensorProduct = tensorProduct();
        System.out.println("Combined Quantum State (Tensor Product):");
        for (int i = 0; i < tensorProduct.length; i++) {
            System.out.println("|" + Integer.toBinaryString(i) + "> = " + tensorProduct[i]);
        }
    }

    public void printTensorProduct() {
        if (qubits.isEmpty()) {
            System.out.println("No qubits available.");
            return;
        }
    
        // Initialize the combined state with the state of the first qubit
        Complex[] combinedState = new Complex[1 << qubits.size()]; // 2^number_of_qubits positions
        combinedState[0] = qubits.get(0).getValue().getZeroAmplitude();
        combinedState[1] = qubits.get(0).getValue().getOneAmplitude();
    
        // Apply the tensor product iteratively for each additional qubit
        for (int i = 1; i < qubits.size(); i++) {
            Qubit currentQubit = qubits.get(i).getValue();
            Complex[] newCombinedState = new Complex[1 << (i + 1)]; // Double the size for the next qubit
    
            for (int j = 0; j < (1 << i); j++) {
                newCombinedState[2 * j] = combinedState[j].mul(currentQubit.getZeroAmplitude());
                newCombinedState[2 * j + 1] = combinedState[j].mul(currentQubit.getOneAmplitude());
            }
    
            combinedState = newCombinedState; // Update the combined state
        }
    
        // Print the resulting combined quantum state
        System.out.println("Combined Quantum State (Tensor Product):");
        for (int i = 0; i < combinedState.length; i++) {
            System.out.printf("|%s> = %s\n", Integer.toBinaryString(i), combinedState[i]);
        }
    }

    /**
     * Measures a subset of qubits and normalizes the remaining qubits.
     * @param qubitIndices the indices of qubits to be measured
     */
    public void measureAndNormalize(int[] qubitIndices) {
        Random random = new Random();
        double norm = 0;

        // Assume a simple measurement that collapses each qubit to |0> or |1> with equal probability
        for (int index : qubitIndices) {
            if (index < 0 || index >= qubits.size()) {
                System.out.println("Invalid qubit index: " + index);
                continue;
            }

            Qubit qubit = qubits.get(index).getValue();
            boolean collapseToOne = random.nextBoolean();

            if (collapseToOne) {
                qubit.setZeroAmplitude(new Complex(0, 0));
                qubit.setOneAmplitude(new Complex(1, 0)); // Collapses to |1>
            } else {
                qubit.setZeroAmplitude(new Complex(1, 0)); // Collapses to |0>
                qubit.setOneAmplitude(new Complex(0, 0));
            }
        }

        // Recompute the norm of the state vector excluding measured qubits
        for (Pair<Locus, Qubit> pair : qubits) {
            if (!contains(qubitIndices, pair.getKey().getIndices()[0])) {
                Qubit qubit = pair.getValue();
                norm += qubit.getZeroAmplitude().abssqr() + qubit.getOneAmplitude().abssqr();
            }
        }

        // Normalize the remaining qubits
        for (Pair<Locus, Qubit> pair : qubits) {
            if (!contains(qubitIndices, pair.getKey().getIndices()[0])) {
                Qubit qubit = pair.getValue();
                qubit.setZeroAmplitude(qubit.getZeroAmplitude().div(Math.sqrt(norm)));
                qubit.setOneAmplitude(qubit.getOneAmplitude().div(Math.sqrt(norm)));
            }
        }
    }

    /**
     * Helper method to check if an array contains a value
     */
    private boolean contains(int[] array, int value) {
        for (int item : array) {
            if (item == value) {
                return true;
            }
        }
        return false;
    }


    public void applyHadamardToQubit3(int qubitIndex) {
        Map<String, Complex> newStateVector = new HashMap<>();
    
        // Go through each state in the existing state vector
        stateVector.forEach((state, amplitude) -> {
            char bit = state.charAt(qubitIndex);
            String flippedBit = bit == '0' ? "1" : "0"; // Flip the bit for the Hadamard operation
    
            String baseState0 = state.substring(0, qubitIndex) + "0" + state.substring(qubitIndex + 1);
            String baseState1 = state.substring(0, qubitIndex) + "1" + state.substring(qubitIndex + 1);
    
            // Hadamard transformation coefficients
            Complex coeff = new Complex(0.7071067811865475, 0); // 1/√2
    
            // Apply Hadamard transformation: |0> becomes (|0> + |1>)/√2 and |1> becomes (|0> - |1>)/√2
            newStateVector.merge(baseState0, amplitude.mul(coeff), Complex::add); // Add to |0>
            if (bit == '0') {
                newStateVector.merge(baseState1, amplitude.mul(coeff), Complex::add); // Add to |1>
            } else {
                newStateVector.merge(baseState1, amplitude.mul(coeff).negate(), Complex::add); // Subtract from |1>
            }
        });
    
        stateVector = newStateVector;
        normalizeStateVector3();
    }

    public void measureQubit(int qubitIndex) {
        Map<String, Complex> newStateVector = new HashMap<>();
        double zeroProbability = stateVector.entrySet().stream()
            .filter(entry -> entry.getKey().charAt(qubitIndex) == '0')
            .mapToDouble(entry -> entry.getValue().abssqr())
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

        stateVector.forEach((state, amplitude) -> {
            if (state.charAt(qubitIndex) == measurementResult.charAt(0)) {
                String newState = state.substring(0, qubitIndex) + state.substring(qubitIndex + 1);
                newStateVector.merge(newState, amplitude.div(normalizationFactor), Complex::add);
            }
        });

        stateVector = newStateVector;
        normalizeStateVector3();

        System.out.println("Measurement result: " + measurementResult);
    }

    
    public void normalizeStateVector3() {
         norms = stateVector.values().stream()
                        .mapToDouble(Complex::abssqr)
                        .sum();
    
        if (Math.abs(norms) < 1e-10) { // Check for very small norm, which indicates numerical stability issues
            System.out.println("Normalization error: Norm is zero or too close to zero.");
            return;
        }
    
        norms = Math.sqrt(norms);
        stateVector.replaceAll((key, value) -> value.div(norms));
    }
    
    public void printStateVector3() {
        stateVector.forEach((key, value) -> {
            if (value.getReal() != 0 || value.getImag() != 0) {  // Check if amplitude is not zero
                System.out.println("|" + key + "> = " + value);
            }
        });
    }
    

    // public void applyHadamardToQubitcla(int qubitIndex) {
    //     Map<String, Complex[]> newStateVector = new HashMap<>();
    
    //     stateVector.forEach((state, amplitudes) -> {
    //         Complex amplitudeZero = amplitudes[0]; // Amplitude for |0>
    //         Complex amplitudeOne = amplitudes[1]; // Amplitude for |1>
    //         Complex coeff = new Complex(0.7071067811865475, 0); // 1/√2
    
    //         Complex[] newAmplitudeZero = { amplitudeZero.mul(coeff), amplitudeOne.mul(coeff) };
    //         Complex[] newAmplitudeOne = { amplitudeZero.mul(coeff), amplitudeOne.mul(coeff).negate() };
    
    //         newStateVector.put(state, newAmplitudeZero);
    //         newStateVector.put(flipBit(state, qubitIndex), newAmplitudeOne);
    //     });
    
    //     stateVector = newStateVector;
    //     normalizeStateVector();
    // }
    
    
}
    



    


