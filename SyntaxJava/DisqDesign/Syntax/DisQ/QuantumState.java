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




public class QuantumState {
   // private List<Pair<Locus, EntangledState>> entangledStates;
    public List<QuantumValue> quantumValues;  // To hold all quantum states
    List<Pair<Locus, Qubit>> qubits;

    public QuantumState() {
        this.qubits = new ArrayList<>();
    }

    public void addQubit(Locus locus, Qubit qubit) {
        qubits.add(new Pair<>(locus, qubit));
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
    




    
    
    

}



    


