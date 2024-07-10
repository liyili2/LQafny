package SyntaxJava.DisqDesign.Syntax.DisQ;

/**
 * Interpreter for quantum operations defined by various UnitaryExpr implementations.
 * This interpreter applies quantum gates and transformations to a QuantumState1 object.
 */
public class DisQInterpreter implements UnitaryExprVisitor {
   
    private QuantumState1 quantumState1; // The quantum state to apply operations on.

    /**
     * Constructor to initialize the DisQInterpreter with a quantum state.
     * @param initialState1 The initial quantum state to operate on.
     */
    public DisQInterpreter(QuantumState1 initialState1) {
        this.quantumState1 = initialState1;
    }

    /**
     * Implements the visit method for the Hadamard gate operation.
     * Applies the Hadamard gate to a specific qubit index in the quantum state.
     * @param hadamard The Hadamard gate object to visit.
     */
    @Override
    public void visit(Hadamard hadamard) {
        int qubitIndex = hadamard.getqubitIndex();
        System.out.println("Applying Hadamard Gate");
        quantumState1.applyHadamardToQubit(qubitIndex);
        quantumState1.printStateVector();
    }

    /**
     * Implements the visit method for the Quantum Fourier Transform (QFT) operation.
     * Applies the QFT operation to the quantum state.
     * @param qft The Quantum Fourier Transform object to visit.
     */
    @Override
    public void visit(QuantumFourierTransform qft) {
        System.out.println("Applying Quantum Fourier Transform");
        quantumState1.applyQFT();
        quantumState1.printStateVector();
    }

    /**
     * Implements the visit method for the Rotation Z (RZ) gate operation.
     * Applies the RZ gate to a specific qubit index with a given angle theta.
     * @param rz The Rotation Z gate object to visit.
     */
    @Override
    public void visit(RotationZ rz) {
        System.out.println("Applying Rotation Z Gate");
        quantumState1.applyRotationZToQubit(rz.qubitIndex, rz.theta);
        quantumState1.printStateVector();
    }

    /**
     * Implements the visit method for the Controlled-NOT (CNOT) gate operation.
     * Applies the CNOT gate to specific control and target qubit indices.
     * @param cx The Controlled-NOT gate object to visit.
     */
    @Override
    public void visit(ControlledNot cx) {
        System.out.println("Applying Controlled-NOT Gate");
        quantumState1.applyControlledXToQubit(cx.control, cx.target);
        quantumState1.printStateVector();
    }

    /**
     * Implements the visit method for the Pauli-X (X) gate operation.
     * Applies the X gate to a specific qubit index.
     * @param X The Pauli-X gate object to visit.
     */
    @Override
    public void visit(PauliX X) {
        System.out.println("Applying X Gate");
        quantumState1.applyXToQubit(X.qubitIndex);
        quantumState1.printStateVector();
    }
}
