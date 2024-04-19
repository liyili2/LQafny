package SyntaxJava.DisqDesign.Syntax.DisQ;

public class ClassicalReceiveAction implements Action {
    private ClassicalChannel channel;
    private String variableName; // Variable to store the received data

    public ClassicalReceiveAction(ClassicalChannel channel, String variableName) {
        this.channel = channel;
        this.variableName = variableName;
    }

    public ClassicalChannel getChannel() {
        return channel;
    }

    public String getVariableName() {
        return variableName;
    }

    @Override
    public void accept(ActionVisitor visitor) {
        visitor.visit(this);
    }
}
