package SyntaxJava.DisqDesign.Syntax.DisQ;

interface Process {
   abstract void accept(ProcessVisitor visitor);
}
