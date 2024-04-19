package SyntaxJava.DisqDesign.Syntax.DisQ;

public class ClassicalSendAction implements Action {
    private ClassicalChannel channel;
    private String message;

    public ClassicalSendAction(ClassicalChannel channel, String message) {
        this.channel = channel;
        this.message = message;
    }

    public ClassicalChannel getChannel() {
        return channel;
    }

    public String getMessage() {
        return message;
    }

    @Override
    public void accept(ActionVisitor visitor) {
        visitor.visit(this);
    }
}
