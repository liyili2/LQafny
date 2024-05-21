package SyntaxJava.DisqDesign.Syntax.DisQ;

public class Qubit {
    

    
        public Complex zeroAmplitude; // Amplitude for |0>
        public Complex oneAmplitude;  // Amplitude for |1>
        boolean IsEntangled =false ;
        int EnQubitindex;
    
        public Qubit(Complex zeroAmplitude, Complex oneAmplitude) {
            this.zeroAmplitude = zeroAmplitude;
            this.oneAmplitude = oneAmplitude;
        }
    
        public void normalize() {
            double norm = Math.sqrt(zeroAmplitude.abssqr() + oneAmplitude.abssqr());
           // System.out.println(zeroAmplitude.abssqr() + oneAmplitude.abssqr());
           // System.out.println(norm);
            zeroAmplitude = zeroAmplitude.div(norm);
            oneAmplitude = oneAmplitude.div(norm);
        }
    
        public Complex getZeroAmplitude() {
            return zeroAmplitude;
        }
    
        public Complex getOneAmplitude() {
            return oneAmplitude;
        }

         // Setters for amplitudes
    public void setZeroAmplitude(Complex amplitude) {
        this.zeroAmplitude = amplitude;
    }

    public void setOneAmplitude(Complex amplitude) {
        this.oneAmplitude = amplitude;
    }
     
    public boolean  getEN()
    {
        return IsEntangled ;
    }
    public int getEntqubitindex()
    {
        return EnQubitindex;
    }

    public  void setEN(boolean IsEntangled,int EnQubitindex)
    {
       this.IsEntangled=IsEntangled ;
       this.EnQubitindex=EnQubitindex;
    }
    
        // Additional methods as needed
    
    
}
