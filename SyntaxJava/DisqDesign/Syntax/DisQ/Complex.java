package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * The Complex class represents complex numbers in a form that combines a real part and an imaginary part.
 * Complex numbers are fundamental to quantum computing, particularly in representing state amplitudes.
 */
public class Complex {
    public float r; // Real part of the complex number.
    public float i; // Imaginary part of the complex number.

    // Constants for commonly used complex numbers
    public static final Complex ZERO = new Complex(0.0, 0.0); // Represents the complex zero.
    public static final Complex ONE = new Complex(1.0, 0.0);  // Represents the complex one.
    public static final Complex I = new Complex(0.0, 1.0);    // Represents the imaginary unit.

    /**
     * Constructor for creating a complex number.
     * @param r The real part of the complex number.
     * @param i The imaginary part of the complex number.
     */
    public Complex(double r, double i) {
        this.r = (float) r;
        this.i = (float) i;
    }

    /**
     * Adds this complex number to another complex number.
     * @param b The complex number to add to this one.
     * @return A new Complex object that is the sum of this and the specified Complex number.
     */
    public Complex add(Complex b) {
        return new Complex(this.r + b.r, this.i + b.i);
    }

    /**
     * Subtracts another complex number from this complex number.
     * @param b The complex number to subtract from this one.
     * @return A new Complex object that is the difference between this and the specified Complex number.
     */
    public Complex sub(Complex b) {
        return new Complex(this.r - b.r, this.i - b.i);
    }

    /**
     * Negates this complex number.
     * @return A new Complex object that is the negation of this complex number.
     */
    public Complex negate() {
        return new Complex(-r, -i);
    }

    /**
     * Multiplies this complex number by another complex number.
     * @param b The complex number to multiply with this one.
     * @return A new Complex object that is the product of this and the specified Complex number.
     */
    public Complex mul(Complex b) {
        return new Complex(
                this.r * b.r - this.i * b.i,
                this.r * b.i + this.i * b.r
        );
    }

    /**
     * Scales this complex number by a real number.
     * @param alpha The real number to scale this complex number by.
     * @return A new Complex object that is the result of scaling this complex number by the specified scalar.
     */
    public Complex scale(double alpha) {
        return new Complex(this.r * alpha, this.i * alpha);
    }

    /**
     * Multiplies this complex number by a real number (scalar multiplication).
     * @param b The scalar to multiply with this complex number.
     * @return A new Complex object that is the result of the scalar multiplication of this complex number.
     */
    public Complex mul(double b) {
        return new Complex(this.r * b, this.i * b);
    }

    /**
     * Calculates the magnitude squared of this complex number, which is often used in quantum mechanics.
     * @return The magnitude squared of this complex number.
     */
    public double abssqr() {
        return this.r * this.r + this.i * this.i;
    }

    /**
     * Divides this complex number by a real divisor.
     * @param divisor The real number to divide this complex number by.
     * @return A new Complex object that is the result of the division.
     */
    public Complex div(double divisor) {
        return new Complex(r / divisor, i / divisor);
    }

    /**
     * Constructs a complex number from polar coordinates, which is useful in quantum mechanics and signal processing.
     * @param magnitude The magnitude of the complex number.
     * @param angle The angle in radians.
     * @return A new Complex object created from the given polar coordinates.
     */
    public static Complex fromPolar(double magnitude, double angle) {
        return new Complex(magnitude * Math.cos(angle), magnitude * Math.sin(angle));
    }

    /**
     * Provides a string representation of the complex number, formatted to enhance readability by trimming very small values.
     * @return A string representation of the complex number.
     */
    @Override
    public String toString() {
        float displayReal = Math.abs(this.r) < 1e-7 ? 0 : this.r;
        float displayImag = Math.abs(this.i) < 1e-7 ? 0 : this.i;
        return "(" + displayReal + ", " + displayImag + ")";
    }

    /**
     * Returns the real part of the complex number.
     * @return The real part as a double.
     */
    public double getReal() {
        return r;
    }

    /**
     * Returns the imaginary part of the complex number.
     * @return The imaginary part as a double.
     */
    public double getImag() {
        return i;
    }

}
