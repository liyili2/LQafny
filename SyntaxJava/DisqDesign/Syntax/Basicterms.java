package SyntaxJava.DisqDesign.Syntax ;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;


class NaturalNumber {
    private int value;

    public NaturalNumber(int value) {
        if (value < 0) {
            throw new IllegalArgumentException("Natural number must be non-negative.");
        }
        this.value = value;
    }

    public int getValue() {
        return value;
    }
}

class ComplexNumber {
    private double real;
    private double imaginary;

    public ComplexNumber(double real, double imaginary) {
        this.real = real;
        this.imaginary = imaginary;
    }

    public double getReal() {
        return real;
    }

    public double getImaginary() {
        return imaginary;
    }

    public ComplexNumber add(ComplexNumber other) {
        return new ComplexNumber(this.real + other.real, this.imaginary + other.imaginary);
    }

    public ComplexNumber subtract(ComplexNumber other) {
        return new ComplexNumber(this.real - other.real, this.imaginary - other.imaginary);
    }

    public ComplexNumber multiply(ComplexNumber other) {
        double newReal = this.real * other.real - this.imaginary * other.imaginary;
        double newImaginary = this.real * other.imaginary + this.imaginary * other.real;
        return new ComplexNumber(newReal, newImaginary);
    }

    public double magnitudeSquared() {
        return real * real + imaginary * imaginary;
    }

    @Override
    public String toString() {
        return "(" + real + " + " + imaginary + "i)";
    }
}

class Variable<T> {
    private T value;

    public void setValue(T value) {
        this.value = value;
    }

    public T getValue() {
        return value;
    }
}

class BitString {
    private List<Boolean> bits;

    public BitString(String bitString) {
        bits = new ArrayList<>();
        for (char bit : bitString.toCharArray()) {
            if (bit == '0') {
                bits.add(false);
            } else if (bit == '1') {
                bits.add(true);
            } else {
                throw new IllegalArgumentException("BitString must contain only 0s and 1s");
            }
        }
    }

    public List<Boolean> getBits() {
        return bits;
    }
}

class Location {
    private int identifier;

    public Location(int identifier) {
        this.identifier = identifier;
    }

    public int getIdentifier() {
        return identifier;
    }
}

enum Bit {
    ZERO, ONE
}

class BasisVector {
    private List<ComplexNumber> vector;

    public BasisVector(List<ComplexNumber> vector) {
        this.vector = vector;
    }

    public List<ComplexNumber> getVector() {
        return vector;
    }
}

// Now adding the QuantumBit class based on the provided definitions
class QuantumBit {
    private ComplexNumber alpha; // Amplitude for |0>
    private ComplexNumber beta;  // Amplitude for |1>

    public QuantumBit() {
        this.alpha = new ComplexNumber(1.0, 0.0); // Start in the |0> state
        this.beta = new ComplexNumber(0.0, 0.0);  // |1> state has zero amplitude
    }

    public void applyHadamard() {
        ComplexNumber newAlpha = alpha.add(beta).multiply(new ComplexNumber(1.0/Math.sqrt(2), 0));
        ComplexNumber newBeta = alpha.subtract(beta).multiply(new ComplexNumber(1.0/Math.sqrt(2), 0));
        alpha = newAlpha;
        beta = newBeta;
    }

    public int measure() {
        double probabilityOfZero = alpha.magnitudeSquared();
        if (new Random().nextDouble() < probabilityOfZero) {
            alpha = new ComplexNumber(1, 0);
            beta = new ComplexNumber(0, 0);
            return 0;
        } else {
            alpha = new ComplexNumber(0, 0);
            beta = new ComplexNumber(1, 0);
            return 1;
        }
    }

    public ComplexNumber getAlpha() {
        return alpha;
    }

    public ComplexNumber getBeta() {
        return beta;
    }
}

