package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.*;

public class ShorsAlgorithm {

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
        System.out.println("Found factorsss: " + sortedFactors);
    }

    private void factorizeHelper(int N, Set<Integer> factors) {
        if (isPrime(N)) {
            factors.add(N);
            return;
        }

        Random rand = new Random();
        boolean factorFound = false;

        while (!factorFound) {
           // int a = 2 + rand.nextInt(N - 2);
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

            if (factor1 != 1 && factor1 != N) {
                factorizeHelper(factor1, factors);
                factorizeHelper(N / factor1, factors);
                factorFound = true;
            }

            if (factor2 != 1 && factor2 != N) {
                factorizeHelper(factor2, factors);
                factorizeHelper(N / factor2, factors);
                factorFound = true;
            }
        }
    }

    private boolean isPrime(int N) {
        if (N <= 1) return false;
        for (int i = 2; i * i <= N; i++) {
            if (N % i == 0) return false;
        }
        return true;
    }

    private int gcd(int a, int b) {
        if (b == 0) return a;
        return gcd(b, a % b);
    }

    private int findPeriod(int a, int N) {
        QuantumState1 qs = new QuantumState1();

        // Initialize quantum state with |0000>
        for (int i = 0; i < 4; i++) {  // Example with 4 qubits for clarity
            qs.addQubit(new Locus(i), new Qubit(new Complex(1, 0), new Complex(0, 0)), "membrane1", 0.25);
        }
           // qs.printStateVector();
        // Apply Hadamard to all qubits
        for (int i = 0; i < 4; i++) {
            qs.applyHadamardToQubit(i);
        }
      //  qs.printStateVector();
        // Apply modular exponentiation
        applyModularExponentiation(qs, a, N);

        // Apply QFT (Quantum Fourier Transform)
        applyQFT(qs);

        // Measure the qubits to find the period
        String measuredValue = measureQubits(qs);

        return extractPeriodFromMeasurement(measuredValue, N);
    }

    private void applyModularExponentiation(QuantumState1 qs, int a, int N) {
        // Placeholder for applying modular exponentiation on the quantum state
        // In a real quantum computer, this would be a quantum circuit
        // Simulating with classical code for now
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

    private void applyQFT(QuantumState1 qs) {
        // Placeholder for applying Quantum Fourier Transform on the quantum state
        // Simulating with classical code for now
        int n = (int) (Math.log(qs.getStateVector().size()) / Math.log(2)); // Number of qubits
        for (int i = 0; i < n; i++) {
            qs.applyHadamardToQubit(i);
            for (int j = i + 1; j < n; j++) {
                double theta = Math.PI / Math.pow(2, j - i);
                qs.applyRotationZToQubit(j, theta);
            }
        }
    }

    private String measureQubits(QuantumState1 qs) {
        // Placeholder for measuring qubits in the quantum state
        // In a real quantum computer, this would collapse the quantum state to a classical state
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

    private int extractPeriodFromMeasurement(String measuredValue, int N) {
        // Placeholder for extracting the period from the measurement result
        // Simulating with classical code for now
        int measuredInt = Integer.parseInt(measuredValue, 2);
        double fraction = (double) measuredInt / Math.pow(2, measuredValue.length());
        return (int) Math.round(1.0 / fraction);
    }

    public static void main(String[] args) {
        ShorsAlgorithm shorsAlgorithm = new ShorsAlgorithm();
        int N = 4911;  // Example with N = 150
        System.out.println("Shor's");
        shorsAlgorithm.factorize(N);
    }
}
