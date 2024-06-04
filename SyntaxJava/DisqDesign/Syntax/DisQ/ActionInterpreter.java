package SyntaxJava.DisqDesign.Syntax.DisQ;

import java.util.Arrays;

public class ActionInterpreter implements ActionVisitor {
    private QuantumState quantumState; 

    public ActionInterpreter(QuantumState quantumState) {
        this.quantumState = quantumState;
    }

    @Override
    public void visit(QuantumOperationAction action) {
        UnitaryExpr operation = action.getOperation();
        //int[] targetQubits = action.getTargetQubits();
        int qubitIndex =action.qubitIndex;
        double theta = action.theta;
        int control = action.control;
        int target = action.target;
        
        //QuantumValue qv = action.qv; 

        
        // Apply the unitary operation to the quantum state
        if (operation instanceof Hadamard) {
            //quantumState.applyHadamard(qubitIndex);
            System.out.println("\nHadamardGate: \n");
           // quantumState.applyHadamardToQubit(qubitIndex);
            quantumState.applyHadamardToQubit3(qubitIndex);
        } else if (operation instanceof PauliX) {
            System.out.println("\nX Gate: \n");
            quantumState.applyXgate(qubitIndex);
        } else if (operation instanceof QuantumFourierTransform) {
            //quantumState.applyQuantumFourierTransform(targetQubits);
            System.out.println("\nQFT Gate: \n");
        } else if (operation instanceof RotationZ) {
           // RotationZ rz = (RotationZ) operation;
           System.out.println("\nRZ Gate: \n");
            quantumState.applyRzToQubit(qubitIndex,theta);
        } else if (operation instanceof ControlledNot) {
            //ControlledNot cn = (ControlledNot) operation;
            System.out.println("\nCNOT Gate: \n");
            quantumState.applyControlXgate(control,target);
        } else if (operation instanceof ControlledU) {
            //ControlledU cu = (ControlledU) operation;
           // quantumState.applyControlledU(cu.getControlQubit(), cu.getInternalUnitary());
        }

        //System.out.println("Applied " + operation.getClass().getSimpleName() + " to qubits " + Arrays.toString(targetQubits));
        quantumState.printQubits();
    }

    @Override
    public void visit(ClassicalSendAction action) {
        System.out.println("Sending message: " + action.getMessage() + " over channel: " + action.getChannel().getIdentifier());
        action.getChannel().send(action.getMessage());
    }

    @Override
    public void visit(ClassicalReceiveAction action) {
        String message = action.getChannel().receive();
        System.out.println("Received message: " + message + " stored in variable: " + action.getVariableName());
    }

    @Override
    public void visit(QuantumMeasurementAction action) {
       // String result = quantumState.measure(action.getTargetQubits());
       // System.out.println("Measurement of qubits " + Arrays.toString(action.getTargetQubits()) + " resulted in: " + result);
      // complex result = quantumState.measure(0);
      // System.out.println("Measurement"+result);
        
    }
}
