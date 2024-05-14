package SyntaxJava.DisqDesign.Syntax.DisQ;

public class Qubit {
    

    
        private Complex zeroAmplitude; // Amplitude for |0>
        private Complex oneAmplitude;  // Amplitude for |1>
    
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
    
        // Additional methods as needed
    
    
}
