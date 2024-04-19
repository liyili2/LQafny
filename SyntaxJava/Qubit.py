import numpy as np
import scipy.linalg

def RotationZ(theta):
    """Generate a RotationZ gate for a given angle theta (in radians)."""
    return np.array([
        [np.exp(-1j * theta / 2), 0],
        [0, np.exp(1j * theta / 2)]
    ])

# Define basic qubit states
Zero = np.array([[1.0], [0.0]])
One = np.array([[0.0], [1.0]])

# Normalize state function
def NormalizeState(state):
    return state / scipy.linalg.norm(state)

# Create a superposition state (Hadamard gate on Zero state)
Hadamard = 1/np.sqrt(2) * np.array([[1, 1], [1, -1]])
Plus = NormalizeState(np.dot(Hadamard, Zero))

# Define a function for Kronecker product of multiple arrays
def NKron(*args):
    result = np.array([[1.0]])
    for op in args:
        result = np.kron(result, op)
    return result

# Example of creating a 5-qubit state
FiveQubitState = NKron(One, Zero, One, Zero, One)

# Hadamard gate applied on the first qubit of a 5-qubit system
Id = np.eye(2)
HadamardZeroOnFive = NKron(Hadamard, Id, Id, Id, Id)
NewState = np.dot(HadamardZeroOnFive, FiveQubitState)

# CNOT gate
P0 = np.dot(Zero, Zero.T)
P1 = np.dot(One, One.T)
X = np.array([[0, 1], [1, 0]])
CNOT03 = NKron(P0, Id, Id, Id, Id) + NKron(P1, Id, Id, X, Id)
NewCNOTState = np.dot(CNOT03, FiveQubitState)

# Applying RotationZ to the third qubit of the 5-qubit state
theta = np.pi / 4  # Example rotation angle
RotationZGate = RotationZ(theta)
RotationZOnThird = NKron(Id, Id, RotationZGate, Id, Id)
RotatedState = np.dot(RotationZOnThird, FiveQubitState)
print("State after applying RotationZ on the third qubit:")
print(RotatedState)

# Measurement of the first qubit in a Cat state
CatState = NormalizeState(NKron(Zero, Zero) + NKron(One, One))
RhoCatState = np.dot(CatState, CatState.T)
Prob0 = np.trace(np.dot(NKron(P0, Id), RhoCatState))
if (np.random.rand() < Prob0):
    Result = 0
    ResultState = NormalizeState(np.dot(NKron(P0, Id), CatState))
else:
    Result = 1
    ResultState = NormalizeState(np.dot(NKron(P1, Id), CatState))

print("Qubit 0 Measurement Result:", Result)
print("Post-Measurement State:")
print(ResultState)

