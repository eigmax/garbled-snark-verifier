use crate::{bag::*, circuits::bn254::fq::Fq};

pub struct G1Projective;

impl G1Projective {
    pub const N_BITS: usize = 3 * Fq::N_BITS;
}

impl G1Projective {
    // http://koclab.cs.ucsb.edu/teaching/ccs130h/2018/09projective.pdf
    pub fn add(p: Wires, q: Wires) -> Circuit {
        assert_eq!(p.len(), Self::N_BITS);
        assert_eq!(q.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let x1 = p[0..Fq::N_BITS].to_vec();
        let y1 = p[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let z1 = p[2*Fq::N_BITS..3*Fq::N_BITS].to_vec();
        let x2 = q[0..Fq::N_BITS].to_vec();
        let y2 = q[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let z2 = q[2*Fq::N_BITS..3*Fq::N_BITS].to_vec();

        let z1s = circuit.extend(Fq::square(z1.clone()));
        let z2s = circuit.extend(Fq::square(z2.clone()));
        let u1 = circuit.extend(Fq::mul(x1.clone(), z2s.clone()));
        let u2 = circuit.extend(Fq::mul(x2.clone(), z1s.clone()));
        let s1 = circuit.extend(Fq::mul(y1.clone(), z2s.clone()));
        let s2 = circuit.extend(Fq::mul(y2.clone(), z1s.clone()));
        let r = circuit.extend(Fq::sub(s1.clone(), s2.clone()));
        let h = circuit.extend(Fq::sub(u1.clone(), u2.clone()));
        let h2 = circuit.extend(Fq::square(h.clone()));
        let g = circuit.extend(Fq::mul(h.clone(), h2.clone()));
        let v = circuit.extend(Fq::mul(u1.clone(), h2.clone()));
        let r2 = circuit.extend(Fq::square(r.clone()));
        let r2g = circuit.extend(Fq::add(r2.clone(), g.clone()));
        let vd = circuit.extend(Fq::double(v.clone()));
        let x3 = circuit.extend(Fq::sub(r2g.clone(), vd.clone()));
        let vx3 = circuit.extend(Fq::sub(v.clone(), x3.clone()));
        let w = circuit.extend(Fq::mul(r.clone(), vx3.clone()));
        let s1g = circuit.extend(Fq::mul(s1.clone(), g.clone()));
        let y3 = circuit.extend(Fq::sub(w.clone(), s1g.clone()));
        let z1z2 = circuit.extend(Fq::mul(z1.clone(), z2.clone()));
        let z3 = circuit.extend(Fq::mul(z1z2.clone(), h.clone()));

        circuit.add_wires(x3);
        circuit.add_wires(y3);
        circuit.add_wires(z3);
    
        circuit
    }

    pub fn double(p: Wires) -> Circuit {
        assert_eq!(p.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let x = p[0..Fq::N_BITS].to_vec();
        let y = p[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let z = p[2*Fq::N_BITS..3*Fq::N_BITS].to_vec();

        let x2 = circuit.extend(Fq::square(x.clone()));
        let y2 = circuit.extend(Fq::square(y.clone()));
        let m = circuit.extend(Fq::triple(x2.clone()));
        let t = circuit.extend(Fq::square(y2.clone()));
        let xy2 = circuit.extend(Fq::mul(x.clone(), y2.clone()));
        let xy2d = circuit.extend(Fq::double(xy2.clone()));
        let s = circuit.extend(Fq::double(xy2d.clone()));
        let m2 = circuit.extend(Fq::square(m.clone()));
        let sd = circuit.extend(Fq::double(s.clone()));
        let xr = circuit.extend(Fq::sub(m2.clone(), sd.clone()));
        let sxr = circuit.extend(Fq::sub(s.clone(), xr.clone()));
        let msxr = circuit.extend(Fq::mul(m.clone(), sxr.clone()));
        let td = circuit.extend(Fq::double(t.clone()));
        let tdd = circuit.extend(Fq::double(td.clone()));
        let tddd = circuit.extend(Fq::double(tdd.clone()));
        let yr = circuit.extend(Fq::sub(msxr.clone(), tddd.clone()));
        let yz = circuit.extend(Fq::mul(y.clone(), z.clone()));
        let zr = circuit.extend(Fq::double(yz.clone()));

        circuit.add_wires(xr);
        circuit.add_wires(yr);
        circuit.add_wires(zr);

        circuit
    }
}

#[cfg(test)]
mod tests {
    use crate::circuits::bn254::utils::{g1p_from_wires, random_g1p, wires_set_from_g1p};
    use super::*;

    #[test]
    fn test_g1p_add() {
        let a = random_g1p();
        let b = random_g1p();
        let circuit = G1Projective::add(wires_set_from_g1p(a.clone()), wires_set_from_g1p(b.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = g1p_from_wires(circuit.0);
        assert_eq!(c, a + b);
    }

    #[test]
    fn test_g1p_double() {
        let a = random_g1p();
        let circuit = G1Projective::double(wires_set_from_g1p(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = g1p_from_wires(circuit.0);
        assert_eq!(c, a + a);
    }
}
