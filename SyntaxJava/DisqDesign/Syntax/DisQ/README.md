# DisQ

This repo contains the JAVA Implementation of DisQ , in which we define the syntax, semantics and DisQ intrepretor. 

## Overview

Quantum algorithms generally demand a large number of qubits, making implementation on a single quantum computer difficult due to limited resources. To solve this problem, we have developed a new system called DisQ. DisQ is a framework designed to facilitate the rewriting of quantum algorithms into their distributed versions. The core of  DisQ is distributed quantum programming language that integrates concepts from the Chemical Abstract Machine (CHAM) and Markov Decision Processes (MDP) to define the quantum concurrent and distributed behaviors.

## Setup

To compile DisQ Code , you will need [JAVA](https://ubuntu.com/tutorials/install-jre#1-overview) 

Assuming you have JAVA installed (following the instructions in the link above), follow the steps below to run the intrepetor and Examples.

## Compiling & Running DisQ

```
# Execution of interpreter 

javac SyntaxJava\DisqDesign\Syntax\DisQ\DisqSimulator.java
java SyntaxJava.DisqDesign.Syntax.DisQ.DisqSimulator

# Execution of Shor's Algorithm

javac SyntaxJava\DisqDesign\Syntax\DisQ\ShorsAlgorithm.java
java SyntaxJava.DisqDesign.Syntax.DisQ.ShorsAlgorithm

# Execution of Distributed Shor's Algorithm 

javac SyntaxJava\DisqDesign\Syntax\DisQ\DistributedShorsAlgorithm.java
java SyntaxJava.DisqDesign.Syntax.DisQ.DistributedShorsAlgorithm

# Execution of DisQ equivalence checker

javac SyntaxJava\DisqDesign\Syntax\DisQ\DisQSimulation.java
java SyntaxJava.DisqDesign.Syntax.DisQ.DisQSimulation
```
*Notes*: 
* Make Sure you should be in the Main Directory where SyntaxJava folder is located otherwise it will throw an error.

## Directory Contents

*Action.java, ActionInterpreter.java, ActionVisitor.java - Base classes and interfaces for actions within the DisQ framework.

*ClassicalChannel.java, ClassicalReceiveAction.java, ClassicalSendAction.java - Components handling classical communication channels and actions.

*Complex.java - A class for handling complex numbers, likely used for quantum state calculations.

*ControlledNot.java, Hadamard.java, PauliX.java, RotationZ.java - Quantum gate implementations.

*DisQInterpreter.java, DisQSimulation.java, DisqSimulator.java - Classes for interpreting and simulating DisQ programs.

*QuantumFourierTransform.java, QuantumMeasurementAction.java, QuantumOperationAction.java - Specific quantum operations, including QFT.

*QuantumState.java, QuantumValue.java, Qubit.java - Core quantum computing constructs.

*ShorsAlgorithm.java, DistributedShorsAlgorithm.java - Implementations of Shor's algorithm, both centralized and distributed.