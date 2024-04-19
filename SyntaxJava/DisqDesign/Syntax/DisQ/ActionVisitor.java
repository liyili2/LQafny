package SyntaxJava.DisqDesign.Syntax.DisQ;

interface ActionVisitor {
    void visit(QuantumOperationAction action);
    void visit(ClassicalSendAction action);
    void visit(ClassicalReceiveAction action);
    void visit(QuantumMeasurementAction action);
}
