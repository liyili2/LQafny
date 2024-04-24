

import java.util.function.BooleanSupplier;
class ConditionalProcess implements Process {
    private BooleanSupplier condition;
    private Process trueProcess;
    private Process falseProcess;

    public ConditionalProcess(BooleanSupplier condition, Process trueProcess, Process falseProcess) {
        this.condition = condition;
        this.trueProcess = trueProcess;
        this.falseProcess = falseProcess;
    }

    public BooleanSupplier getCondition() { return condition; }
    public Process getTrueProcess() { return trueProcess; }
    public Process getFalseProcess() { return falseProcess; }

    @Override
    public void accept(ProcessVisitor visitor) {
        visitor.visit(this);
    }
}
