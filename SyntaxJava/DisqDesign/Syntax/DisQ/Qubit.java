package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Represents a quantum bit (qubit) with complex amplitudes for |0> and |1>.
 */
public class Qubit {
    public Complex zeroAmplitude; // Amplitude for |0>
    public Complex oneAmplitude;  // Amplitude for |1>
    boolean IsEntangled = false; // Flag indicating if the qubit is entangled
    int EnQubitindex; // Index of the entangled qubit

    /**
     * Constructor for initializing a qubit with specified zero and one amplitudes.
     * @param zeroAmplitude The complex amplitude for |0>.
     * @param oneAmplitude The complex amplitude for |1>.
     */
    public Qubit(Complex zeroAmplitude, Complex oneAmplitude) {
        this.zeroAmplitude = zeroAmplitude;
        this.oneAmplitude = oneAmplitude;
    }

    /**
     * Normalizes the qubit by dividing each amplitude by the square root of their combined squared magnitudes.
     */
    public void normalize() {
        double norm = Math.sqrt(zeroAmplitude.abssqr() + oneAmplitude.abssqr());
        zeroAmplitude = zeroAmplitude.div(norm);
        oneAmplitude = oneAmplitude.div(norm);
    }

    /**
     * Retrieves the complex amplitude for |0>.
     * @return The complex amplitude for |0>.
     */
    public Complex getZeroAmplitude() {
        return zeroAmplitude;
    }

    /**
     * Retrieves the complex amplitude for |1>.
     * @return The complex amplitude for |1>.
     */
    public Complex getOneAmplitude() {
        return oneAmplitude;
    }

    /**
     * Sets the amplitude for |0>.
     * @param amplitude The new complex amplitude for |0>.
     */
    public void setZeroAmplitude(Complex amplitude) {
        this.zeroAmplitude = amplitude;
    }

    /**
     * Sets the amplitude for |1>.
     * @param amplitude The new complex amplitude for |1>.
     */
    public void setOneAmplitude(Complex amplitude) {
        this.oneAmplitude = amplitude;
    }

    /**
     * Retrieves the entanglement status of the qubit.
     * @return True if the qubit is entangled, false otherwise.
     */
    public boolean getEN() {
        return IsEntangled;
    }

    /**
     * Retrieves the index of the qubit with which this qubit is entangled.
     * @return The index of the entangled qubit.
     */
    public int getEntqubitindex() {
        return EnQubitindex;
    }

    /**
     * Sets the entanglement status and index of the entangled qubit.
     * @param IsEntangled True if the qubit is entangled, false otherwise.
     * @param EnQubitindex The index of the entangled qubit.
     */
    public void setEN(boolean IsEntangled, int EnQubitindex) {
        this.IsEntangled = IsEntangled;
        this.EnQubitindex = EnQubitindex;
    }
}
