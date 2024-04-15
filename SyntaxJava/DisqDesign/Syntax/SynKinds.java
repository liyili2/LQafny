package SyntaxJava.DisqDesign.Syntax ;
import java.util.ArrayList;
import java.util.List;





public class SynKinds {

    enum Kind {
        CLASSICAL, // Represents a classical value
        QUANTUM    // Represents a quantum value with a location identifier and length
    }

    class ClassicalScalarValue {
        private int value;

        public ClassicalScalarValue(int value) {
            this.value = value;
        }

        public int getValue() {
            return value;
        }
    }

    class FrozenBasisStack {
        private List<BasisVector> stack;

        public FrozenBasisStack() {
            this.stack = new ArrayList<>();
        }

        public void addBasisVector(BasisVector basisVector) {
            stack.add(basisVector);
        }

        public List<BasisVector> getStack() {
            return stack;
        }
    }

    class FullBasisVector {
        private BasisVector basisVector;
        private FrozenBasisStack frozenStack;

        public FullBasisVector(BasisVector basisVector, FrozenBasisStack frozenStack) {
            this.basisVector = basisVector;
            this.frozenStack = frozenStack;
        }

        public BasisVector getBasisVector() {
            return basisVector;
        }

        public FrozenBasisStack getFrozenStack() {
            return frozenStack;
        }
    }

    class BasicKet {
        private ComplexNumber amplitude;
        private FullBasisVector fullBasisVector;

        public BasicKet(ComplexNumber amplitude, FullBasisVector fullBasisVector) {
            this.amplitude = amplitude;
            this.fullBasisVector = fullBasisVector;
        }

        public ComplexNumber getAmplitude() {
            return amplitude;
        }

        public FullBasisVector getFullBasisVector() {
            return fullBasisVector;
        }
    }

    class QuantumType {
        // Placeholder for the details of the quantum type
        char QT ;

       
        public QuantumType (char QT)
        {
            this.QT = QT;
        }
    }

    

    class QuantumValue {
        private List<BasicKet> kets;

        public QuantumValue() {
            this.kets = new ArrayList<>();
        }

        public void addKet(BasicKet ket) {
            kets.add(ket);
        }

        public List<BasicKet> getKets() {
            return kets;
        }

        
    }

   
    
}
