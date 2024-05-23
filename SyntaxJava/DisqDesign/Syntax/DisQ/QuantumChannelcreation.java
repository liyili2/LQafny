package SyntaxJava.DisqDesign.Syntax.DisQ;

public class QuantumChannelcreation implements Membrane {
    Membraneprocess source = new Membraneprocess() ;
    Membraneprocess partner = new Membraneprocess() ;
    int numQubits ;

        //Constructor creation for Quantum channel creation
    QuantumChannelcreation(Membraneprocess source ,Membraneprocess partner, int numQubits )
    {
        this.source = source;
        this.partner = partner ;
        this.numQubits=numQubits;
       // createEPRPair( source ,partner,numQubits) ;

    }
      //  Membraneprocess membraneprocess = new Membraneprocess();

    //Sendings signal or messages to other membranes.
      public void sendsignals ( String signals)
      {
        partner.receiveMessage(signals);
      }

        //EPR Pair creation for both the membranses
    public void createEPRPair(Membraneprocess source ,Membraneprocess partner, int numQubits) {
        for (int i = 0; i < numQubits; i++) {
            Qubit q1 = new Qubit(new Complex(1 / Math.sqrt(2), 0), new Complex(1 / Math.sqrt(2), 0));
            Qubit q2 = new Qubit(new Complex(1 / Math.sqrt(2), 0), new Complex(1 / Math.sqrt(2), 0));
            Locus sourceloci = new Locus(source.getnumberofqubits());
            Locus partnerloci = new Locus(partner.getnumberofqubits());
            source.Addqubits(sourceloci ,q1);
            partner.Addqubits(partnerloci,q2);
        }
        System.out.println("EPR pair created between " + source.getLocation()+ " and " + partner.getLocation());
    }

    @Override
    public void accept(MembraneVisitor visitor) {
        visitor.visit(this);
    }
    
}
