package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.*;

/**
 * Implements Shor's Algorithm for integer factorization using a quantum-inspired approach.
 * This class demonstrates the algorithm's steps using classical simulation methods.
 */
public class ShorsAlgorithm {

    /**
     * Factorizes the given integer N using Shor's Algorithm.
     * @param N The integer to factorize.
     */
    public void factorize(int N) {
        if (N <= 1) {
            System.out.println("Invalid input: N must be greater than 1.");
            return;
        }

        if (isPrime(N)) {
            System.out.println(N + " is a prime number.");
            return;
        }

        // Set to store factors found
        Set<Integer> factors = new HashSet<>();
        factorizeHelper(N, factors);

        // Sorting and printing the factors
        List<Integer> sortedFactors = new ArrayList<>(factors);
        Collections.sort(sortedFactors);
        System.out.println("Found factors: " + sortedFactors);
    }

    /**
     * Helper method to recursively find factors of N using quantum-inspired techniques.
     * @param N The integer to factorize.
     * @param factors Set to store the factors found.
     */
    private void factorizeHelper(int N, Set<Integer> factors) {
        // If N is prime, add N as a factor
        if (isPrime(N)) {
            factors.add(N);
            return;
        }

        Random rand = new Random();
        boolean factorFound = false;

        // Loop until a non-trivial factor is found
        while (!factorFound) {
            // Choose a random integer 'a' between 2 and N-1
            int a = 2 + rand.nextInt(Math.max(1, N - 2));

            // Compute gcd(a, N)
            int gcd = gcd(a, N);
            if (gcd != 1 && gcd != N) {
                // If gcd(a, N) is a non-trivial factor, recursively factorize
                factorizeHelper(gcd, factors);
                factorizeHelper(N / gcd, factors);
                factorFound = true;
                continue;
            }

            // Find the period 'r' of 'a' mod N using Quantum Fourier Transform approach
            int r = findPeriod(a, N);

            // Check if 'r' is even and satisfies additional conditions
            if (r % 2 != 0) continue;
            if (Math.pow(a, r / 2) % N == N - 1) continue;

            // Calculate potential factors using the period 'r'
            int factor1 = gcd((int) Math.pow(a, r / 2) - 1, N);
            int factor2 = gcd((int) Math.pow(a, r / 2) + 1, N);

            // If factors are found, recursively factorize
            if (factor1 != 1 && factor1 != N && factor1 > 0) {
                factorizeHelper(factor1, factors);
                factorizeHelper(N / factor1, factors);
                factorFound = true;
            }

            if (factor2 != 1 && factor2 != N && factor2 > 0) {
                factorizeHelper(factor2, factors);
                factorizeHelper(N / factor2, factors);
                factorFound = true;
            }
        }
    }

    /**
     * Checks if a number is prime.
     * @param N The number to check.
     * @return true if N is prime, false otherwise.
     */
    private boolean isPrime(int N) {
        if (N <= 1) return false;
        for (int i = 2; i * i <= N; i++) {
            if (N % i == 0) return false;
        }
        return true;
    }

    /**
     * Computes the greatest common divisor (gcd) of two integers.
     * @param a First integer.
     * @param b Second integer.
     * @return The gcd of 'a' and 'b'.
     */
    private int gcd(int a, int b) {
        if (b == 0) return a;
        return gcd(b, a % b);
    }

    /**
     * Simulates the process of finding the period 'r' of 'a' mod N using Quantum Fourier Transform.
     * @param a The base integer.
     * @param N The integer to factorize.
     * @return The period 'r' of 'a' mod N.
     */
    private int findPeriod(int a, int N) {
        // Create a quantum state representing |0000> (example with 4 qubits)
        QuantumState1 qs = new QuantumState1();
        for (int i = 0; i < 4; i++) {
            qs.addQubit(new Locus(i), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.25);
        }

        // Apply Hadamard transform to all qubits
        for (int i = 0; i < 4; i++) {
            qs.applyHadamardToQubit(i);
        }

        // Apply modular exponentiation
        applyModularExponentiation(qs, a, N);

        // Apply Quantum Fourier Transform
        applyQFT(qs);

        // Measure qubits to find the period 'r'
        String measuredValue = measureQubits(qs);

        // Extract and return the period 'r'
        return extractPeriodFromMeasurement(measuredValue, N);
    }

    /**
     * Simulates the process of applying modular exponentiation on a quantum state.
     * @param qs The quantum state to operate on.
     * @param a The base integer.
     * @param N The integer to factorize.
     */
    private void applyModularExponentiation(QuantumState1 qs, int a, int N) {
        // Simulated method for applying modular exponentiation
        // In a real quantum system, this would be done using quantum gates
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>();

        qs.getStateVector().forEach((state, pair) -> {
            int x = Integer.parseInt(state, 2);
            int f = (int) Math.pow(a, x) % N;
            String newState = Integer.toBinaryString(f);
            while (newState.length() < 4) newState = "0" + newState;  // Ensuring 4-bit representation
            newStateVector.put(newState, pair);
        });

        qs.setStateVector(newStateVector);
        qs.normalizeStateVector();
    }

    /**
     * Simulates the process of applying Quantum Fourier Transform (QFT) on a quantum state.
     * @param qs The quantum state to operate on.
     */
    private void applyQFT(QuantumState1 qs) {
        // Simulated method for applying Quantum Fourier Transform
        // In a real quantum system, this would be done using quantum gates
        int n = (int) (Math.log(qs.getStateVector().size()) / Math.log(2)); // Number of qubits
        for (int i = 0; i < n; i++) {
            qs.applyHadamardToQubit(i);
            for (int j = i + 1; j < n; j++) {
                double theta = Math.PI / Math.pow(2, j - i);
                qs.applyRotationZToQubit(j, theta);
            }
        }
    }

    /**
     * Simulates the process of measuring qubits in a quantum state to obtain a classical result.
     * @param qs The quantum state to measure.
     * @return The measured binary value representing the state.
     */
    private String measureQubits(QuantumState1 qs) {
        // Simulated method for measuring qubits in a quantum state
        // In a real quantum system, this would collapse the state probabilistically
        Random random = new Random();
        List<String> states = new ArrayList<>(qs.getStateVector().keySet());
        double[] probabilities = new double[states.size()];
        for (int i = 0; i < states.size(); i++) {
            probabilities[i] = qs.getStateVector().get(states.get(i)).getKey().abssqr();
        }

        double p = random.nextDouble();
        double cumulativeProbability = 0.0;
        for (int i = 0; i < probabilities.length; i++) {
            cumulativeProbability += probabilities[i];
            if (p <= cumulativeProbability) {
                return states.get(i);
            }
        }

        return states.get(states.size() - 1);  // Should not reach here
    }

    /**
     * Extracts the period 'r' from the measured binary value and computes the factor using it.
     * @param measuredValue The measured binary value from qubit measurement.
     * @param N The integer to factorize.
     * @return The period 'r' extracted from the measurement.
     */
    private int extractPeriodFromMeasurement(String measuredValue, int N) {
        // Simulated method for extracting the period from measurement
        // In a real quantum system, this would involve post-processing of measurement results
        int measuredInt = Integer.parseInt(measuredValue, 2);
        double fraction = (double) measuredInt / Math.pow(2, measuredValue.length());
        return (int) Math.round(1.0 / fraction);
    }

    /**
     * Main method to demonstrate Shor's Algorithm with an example integer N.
     * @param args Command-line arguments (not used).
     */
    public static void main(String[] args) {
        ShorsAlgorithm shorsAlgorithm = new ShorsAlgorithm();
        int N=1234567899 ;  // Example integer to factorize
        
        System.out.println("Shor's Algorithm:");
        System.out.println("Prime factors for "+N+": ");
        shorsAlgorithm.factorize(N);
        
    }
}
