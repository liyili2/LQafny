package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.*;

/**
 * Class implementing a distributed version of Shor's algorithm for integer factorization.
 */
public class DistributedShorsAlgorithm {

    /**
     * Main method to demonstrate the distributed Shor's algorithm.
     * @param args Command-line arguments (not used).
     */
    public static void main(String[] args) {
        DistributedShorsAlgorithm algorithm = new DistributedShorsAlgorithm();
        int N = 1234567899; // Example with N = 1234567899
        System.out.println("Shor's Algorithm:");
        System.out.println("Prime factors for "+N+": ");
        algorithm.factorize(N);
    }

    /**
     * Method to factorize an integer N using distributed Shor's algorithm.
     * @param N Integer to factorize.
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

        Set<Integer> factors = new HashSet<>();
        factorizeHelper(N, factors);

        List<Integer> sortedFactors = new ArrayList<>(factors);
        Collections.sort(sortedFactors);
        System.out.println("Found factors: " + sortedFactors);
    }

    /**
     * Helper method to recursively find factors of N using quantum algorithms.
     * @param N Integer to factorize.
     * @param factors Set to store found factors.
     */
    private void factorizeHelper(int N, Set<Integer> factors) {
        if (isPrime(N)) {
            factors.add(N);
            return;
        }

        Random rand = new Random();
        boolean factorFound = false;

        while (!factorFound) {
            int a = 2 + rand.nextInt(Math.max(1, N - 2));
            int gcd = gcd(a, N);
            if (gcd != 1 && gcd != N) {
                factorizeHelper(gcd, factors);
                factorizeHelper(N / gcd, factors);
                factorFound = true;
                continue;
            }

            int r = findPeriod(a, N);
            if (r % 2 != 0) continue;
            if (Math.pow(a, r / 2) % N == N - 1) continue;

            int factor1 = gcd((int) Math.pow(a, r / 2) - 1, N);
            int factor2 = gcd((int) Math.pow(a, r / 2) + 1, N);

            if (factor1 != 1 && factor1 != N && factor1 >0) {
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
     * Method to check if an integer is prime.
     * @param N Integer to check.
     * @return True if N is prime, false otherwise.
     */
    private boolean isPrime(int N) {
        if (N <= 1) return false;
        for (int i = 2; i * i <= N; i++) {
            if (N % i == 0) return false;
        }
        return true;
    }

    /**
     * Method to compute the greatest common divisor (GCD) of two integers a and b.
     * @param a First integer.
     * @param b Second integer.
     * @return GCD of a and b.
     */
    private int gcd(int a, int b) {
        if (b == 0) return a;
        return gcd(b, a % b);
    }

    /**
     * Method to find the period of a function f(x) = a^x mod N using quantum algorithms.
     * @param a Base of the exponentiation.
     * @param N Modulus.
     * @return Period r of the function f(x).
     */
    private int findPeriod(int a, int N) {
        Membraneprocess membraneL = new Membraneprocess("membraneL");
        Membraneprocess membraneR = new Membraneprocess("membraneR");
        Membraneprocess membraneT = new Membraneprocess("membraneT");

        // Initialize quantum state with |0000> in membraneL
        for (int i = 0; i < 4; i++) {
            membraneL.Addqubits(new Locus(i), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membraneL", 0.25);
        }

        // Apply Hadamard to all qubits in membraneL and teleport to membraneR
        for (int i = 0; i < 4; i++) {
            membraneL.getQuantumState().applyHadamardToQubit(i);
            teleportQubit(membraneL, membraneR, i);
        }

        // Apply modular exponentiation in membraneR and teleport to membraneT
        applyModularExponentiation(membraneR.getQuantumState(), a, N);
        for (int i = 0; i < 4; i++) {
            teleportQubit(membraneR, membraneT, i);
        }

        // Apply Quantum Fourier Transform (QFT) in membraneT
        applyQFT(membraneT.getQuantumState());

        // Measure the qubits in membraneT
        String measuredValue = measureQubits(membraneT.getQuantumState());

        // Extract the period from the measurement result
        return extractPeriodFromMeasurement(measuredValue, N);
    }

    /**
     * Method to simulate the teleportation of a qubit from a source membrane to a target membrane.
     * @param sourceMembrane Source membrane.
     * @param targetMembrane Target membrane.
     * @param qubitIndex Index of the qubit to teleport.
     */
    private void teleportQubit(Membraneprocess sourceMembrane, Membraneprocess targetMembrane, int qubitIndex) {
        QuantumState1 sourceState = sourceMembrane.getQuantumState();
        QuantumState1 targetState = targetMembrane.getQuantumState();

        // Simulate teleportation by copying the state from source to target
        Map<String, Pair<Complex, String>> newStateVector = new HashMap<>(targetState.getStateVector());
        sourceState.getStateVector().forEach((state, pair) -> {
            if (state.charAt(qubitIndex) == '1') {
                String newState = state.substring(0, qubitIndex) + '1' + state.substring(qubitIndex + 1);
                newStateVector.merge(newState, new Pair<>(pair.getKey(), targetMembrane.getLocation()), (oldVal, newVal) -> new Pair<>(oldVal.getKey().add(newVal.getKey()), newVal.getValue()));
            }
        });

        targetState.setStateVector(newStateVector);
        targetState.normalizeStateVector();
    }

    /**
     * Method to apply modular exponentiation f(x) = a^x mod N on a quantum state.
     * @param qs Quantum state to apply the operation on.
     * @param a Base of the exponentiation.
     * @param N Modulus.
     */
    private void applyModularExponentiation(QuantumState1 qs, int a, int N) {
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
     * Method to apply Quantum Fourier Transform (QFT) on a quantum state.
     * @param qs Quantum state to apply QFT on.
     */
    private void applyQFT(QuantumState1 qs) {
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
     * Method to measure qubits in a quantum state and return the measured value.
     * @param qs Quantum state to measure.
     * @return Measured value in binary string format.
     */
    private String measureQubits(QuantumState1 qs) {
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
     * Method to extract the period from the measured value obtained from QFT.
     * @param measuredValue Measured value in binary string format.
     * @param N Integer N used in the algorithm.
     * @return Period extracted from the measured value.
     */
    private int extractPeriodFromMeasurement(String measuredValue, int N) {
        int measuredInt = Integer.parseInt(measuredValue, 2);
        double fraction = (double) measuredInt / Math.pow(2, measuredValue.length());
        return (int) Math.round(1.0 / fraction);
    }
}
