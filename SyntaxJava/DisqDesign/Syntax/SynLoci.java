package DisqDesign.Syntax ;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import DisqDesign.Syntax.SynKinds.*;




public class SynLoci {


     // Represents a range of qubits
    class QubitArrayRange {
        private int start;
        private int end;

        public QubitArrayRange(int start, int end) {
            this.start = start;
            this.end = end;
        }

        // Getter methods for start and end
        public int getStart() {
            return start;
        }

        public int getEnd() {
            return end;
        }
    }

    // Represents a group of qubit ranges, indicating a composite part of the system where qubits might be entangled
    class Locus {
        private List<QubitArrayRange> ranges;

        public Locus() {
            this.ranges = new ArrayList<>();
        }

        public void addRange(QubitArrayRange range) {
            ranges.add(range);
        }

        // Getter method for ranges
        public List<QubitArrayRange> getRanges() {
            return ranges;
        }
    }

    // Similar to a locus, but specifies qubits across potentially multiple locations in a distributed system
    class GlobalLocus {
        private Locus locus;
        private int locationId;

        public GlobalLocus(Locus locus, int locationId) {
            this.locus = locus;
            this.locationId = locationId;
        }

        // Getter methods for locus and locationId
        public Locus getLocus() {
            return locus;
        }

        public int getLocationId() {
            return locationId;
        }
    }

    // A mapping of variables to their kinds (classical or quantum)
    class KindEnvironment {
        private Map<String, Kind> environment;

        public KindEnvironment() {
            this.environment = new HashMap<>();
        }

        public void addVariable(String variableName, Kind kind) {
            environment.put(variableName, kind);
        }

        // Getter method for environment
        public Map<String, Kind> getEnvironment() {
            return environment;
        }
    }

    // A mapping from global loci to quantum types
    class TypeEnvironment {
        private Map<GlobalLocus, QuantumType> types;

        public TypeEnvironment() {
            this.types = new HashMap<>();
        }

        public void addType(GlobalLocus locus, QuantumType type) {
            types.put(locus, type);
        }

        // Getter method for types
        public Map<GlobalLocus, QuantumType> getTypes() {
            return types;
        }
    }

    // The state of the quantum system, associating global loci with their quantum values
    class QuantumState {
        private Map<GlobalLocus, QuantumValue> state;

        public QuantumState() {
            this.state = new HashMap<>();
        }

        public void addState(GlobalLocus locus, QuantumValue value) {
            state.put(locus, value);
        }

        // Getter method for state
        public Map<GlobalLocus, QuantumValue> getState() {
            return state;
        }
    }
    
}
