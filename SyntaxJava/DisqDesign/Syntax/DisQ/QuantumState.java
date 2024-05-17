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
            //System.out.println("\n");
        }
        System.out.println("\n");
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

    public void applyXgate (int qubitIndex)
    {
        if (qubitIndex < 0 || qubitIndex >= qubits.size()) {
            System.out.println("Invalid qubit index.");
            return;
        }
        Pair<Locus, Qubit> pair = qubits.get(qubitIndex);
        Qubit qubit = pair.getValue();
        Complex temp = qubit.zeroAmplitude;
        qubit.zeroAmplitude = qubit.oneAmplitude;
        qubit.oneAmplitude = temp;

    }

    public void applyControlXgate (int control, int target)
    {
        if ((control < 0 && target < 0)|| (control >= qubits.size() && target >= qubits.size())) {
            System.out.println("Invalid qubit index.");
            return;
        }
        Pair<Locus, Qubit> cqubit = qubits.get(control);
        Pair<Locus,Qubit> tqubit = qubits.get(target);

        Qubit controlqubit = cqubit.getValue();
        Qubit targetqubit = tqubit.getValue();

        if (controlqubit.oneAmplitude.r> 0)
        {
        Complex temp = targetqubit.zeroAmplitude;
        targetqubit.zeroAmplitude = targetqubit.oneAmplitude;
        targetqubit.oneAmplitude = temp;
        }

    }

    public void applyRzToQubit(int qubitIndex, double theta) {
        if (qubitIndex < 0 || qubitIndex >= qubits.size()) {
            System.out.println("Invalid qubit index.");
            return;
        }
        Pair<Locus, Qubit> pair = qubits.get(qubitIndex);
        Qubit qubit = pair.getValue();
    
        // Apply phase shift to the |1> amplitude
        Complex phaseFactor = Complex.fromPolar(1, theta); // Creating a complex number with magnitude 1 and phase theta
        Complex newOneAmplitude = qubit.getOneAmplitude().mul(phaseFactor);
    
        // Set the new amplitude for |1>
        qubit.setOneAmplitude(newOneAmplitude);
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

    public void printTensorProduct() {
        Complex[] tensorProduct = tensorProduct();
        System.out.println("Combined Quantum State (Tensor Product):");
        for (int i = 0; i < tensorProduct.length; i++) {
            System.out.println("|" + Integer.toBinaryString(i) + "> = " + tensorProduct[i]);
        }
    }




    
    
    

}



    


