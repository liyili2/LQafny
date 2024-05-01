
package SyntaxJava.DisqDesign.Syntax.DisQ;

public class Complex {
    public float r; // Real part
    public float i; // Imaginary part

    // Constants for commonly used complex numbers
    public static final Complex ZERO = new Complex(0.0, 0.0);
    public static final Complex ONE = new Complex(1.0, 0.0);
    public static final Complex I = new Complex(0.0, 1.0);

    // Constructor
    public Complex(double r, double i) {
        this.r = (float) r;
        this.i = (float) i;
    }

    // Addition of two complex numbers
    public Complex add(Complex b) {
        return new Complex(this.r + b.r, this.i + b.i);
    }

    // Multiplication of two complex numbers
    public Complex mul(Complex b) {
        return new Complex(
                this.r * b.r - this.i * b.i,
                this.r * b.i + this.i * b.r
        );
    }

    // Scalar multiplication
    public Complex mul(double b) {
        return new Complex(this.r * b, this.i * b);
    }

    // Method to calculate the magnitude squared of the complex number
    public double abssqr() {
        return this.r * this.r + this.i * this.i;
    }

    // Utility method to generate a string representation of the complex number
    @Override
    public String toString() {
        // Trim the small values for readability
        float displayReal = Math.abs(this.r) < 1e-7 ? 0 : this.r;
        float displayImag = Math.abs(this.i) < 1e-7 ? 0 : this.i;

        return "(" + displayReal + ", " + displayImag + ")";
    }

    
}