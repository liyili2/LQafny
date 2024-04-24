
class NoOp implements Process {
    @Override
    public void accept(ProcessVisitor visitor) {
        visitor.visit(this);
    }
}