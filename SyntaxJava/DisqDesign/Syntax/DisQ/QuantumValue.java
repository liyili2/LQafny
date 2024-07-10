package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents the quantum state of a multi-qubit system with complex amplitudes.
 */
public class QuantumValue {
    private Complex[] amplitudes; // Array to store complex amplitudes of quantum states

    /**
     * Constructor for initializing a quantum state with zero amplitudes for a given number of qubits.
     * @param numQubits The number of qubits in the quantum state.
     */
    public QuantumValue(int numQubits) {
        this.amplitudes = new Complex[1 << numQubits]; // Allocate space for 2^numQubits states
        for (int i = 0; i < amplitudes.length; i++) {
            amplitudes[i] = Complex.ZERO; // Initialize all amplitudes to zero
        }
    }

    /**
     * Constructor for initializing a quantum state with provided complex amplitudes.
     * @param amplitudes The array of complex amplitudes representing the quantum state.
     */
    public QuantumValue(Complex[] amplitudes) {
        this.amplitudes = amplitudes; // Initialize with provided amplitudes
    }

    /**
     * Retrieves the array of complex amplitudes representing the quantum state.
     * @return The array of complex amplitudes.
     */
    public Complex[] getAmplitudes() {
        return amplitudes;
    }

    /**
     * Retrieves the complex amplitude at the specified index.
     * @param index The index of the amplitude to retrieve.
     * @return The complex amplitude at the specified index.
     */
    public Complex getAmplitude(int index) {
        return amplitudes[index];
    }

    /**
     * Sets the complex amplitude at the specified index.
     * @param index The index of the amplitude to set.
     * @param amplitude The complex amplitude to set.
     */
    public void setAmplitude(int index, Complex amplitude) {
        amplitudes[index] = amplitude;
    }

    /**
     * Normalizes the quantum state by dividing each amplitude by the square root of the sum of their squared magnitudes.
     */
    public void normalize() {
        double sum = 0.0;
        for (Complex amp : amplitudes) {
            sum += amp.abssqr(); // Calculate sum of squared magnitudes
        }
        double normalizationFactor = 1 / Math.sqrt(sum); // Calculate normalization factor
        for (int i = 0; i < amplitudes.length; i++) {
            amplitudes[i] = amplitudes[i].mul(normalizationFactor); // Normalize each amplitude
        }
    }
}
