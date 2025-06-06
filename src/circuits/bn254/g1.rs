use crate::{bag::*, circuits::bn254::fq::Fq};

pub struct G1Projective;

impl G1Projective {
    pub const N_BITS: usize = 3 * Fq::N_BITS;
}

impl G1Projective {
    pub fn add(p: Wires, q: Wires) -> Circuit {
        assert_eq!(p.len(), Self::N_BITS);
        assert_eq!(q.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let px = p[0..Fq::N_BITS].to_vec();
        let py = p[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let pz = p[2*Fq::N_BITS..3*Fq::N_BITS].to_vec();
        let qx = q[0..Fq::N_BITS].to_vec();
        let qy = q[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let qz = q[2*Fq::N_BITS..3*Fq::N_BITS].to_vec();

        todo!();

        circuit
    }

    pub fn double(p: Wires) -> Circuit {
        assert_eq!(p.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let px = p[0..Fq::N_BITS].to_vec();
        let py = p[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let pz = p[2*Fq::N_BITS..3*Fq::N_BITS].to_vec();

        todo!();

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
