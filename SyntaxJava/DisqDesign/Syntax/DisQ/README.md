# DisQ

This repo contains the JAVA definition of DisQ, in which we define the syntax, semantics and DisQ intrepretor. 

## Overview

Quantum algorithms generally demand a large number of qubits, making implementation on a single quantum computer difficult due to limited resources. To solve this problem, we have developed a new system called DisQ. DisQ is a framework designed to facilitate the rewriting of quantum algorithms into their distributed versions. The core of  DisQ is distributed quantum programming language that integrates concepts from the Chemical Abstract Machine (CHAM) and Markov Decision Processes (MDP) to define the quantum concurrent and distributed behaviors.

## Setup

To compile DisQ Code , you will need [JAVA](https://ubuntu.com/tutorials/install-jre#1-overview) 

Assuming you have JAVA installed (following the instructions in the link above), follow the steps below to run the intrepetor and Examples.
```
# Execution of interpreter
javac SyntaxJava\DisqDesign\Syntax\DisQ\DisqSimulator.java
java SyntaxJava\DisqDesign\Syntax\DisQ\DisqSimulator
```
