use ark_ec::pairing::{MillerLoopOutput, Pairing};
use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ff::Field;
use crate::bag::*;
use crate::circuits::bn254::fq12::Fq12;
use crate::circuits::bn254::g1::G1Projective;
use crate::circuits::bn254::pairing::multi_miller_loop_groth16_circuit_evaluate;
use crate::circuits::bn254::utils::{fq12_from_wires, fr_from_wires, wires_set_from_fq12, wires_set_from_g1p};

pub fn fq12_mul_evaluate(a: Wires, b: Wires) -> (Wires, usize) {
    let circuit = Fq12::mul(a, b);

    let n = circuit.1.len();

    for mut gate in circuit.1 {
        gate.evaluate();
    }

    (circuit.0, n)
}

pub fn fq12_equal_constant_evaluate(a: Wires, b: ark_bn254::Fq12) -> (Wires, usize) {
    let circuit = Fq12::equal_constant(a, b);

    let n = circuit.1.len();

    for mut gate in circuit.1 {
        gate.evaluate();
    }

    (circuit.0, n)
}

pub fn groth16_verifier(public: Vec<ark_bn254::Fr>, proof: ark_groth16::Proof<ark_bn254::Bn254>, vk: ark_groth16::VerifyingKey<ark_bn254::Bn254>) -> bool {
    let scalars = [
        vec![ark_bn254::Fr::ONE],
        public.clone(),
    ]
    .concat();
    let msm = ark_bn254::G1Projective::msm(&vk.gamma_abc_g1, &scalars).unwrap();
    let qap = ark_bn254::Bn254::multi_miller_loop([msm, proof.c.into_group(), proof.a.into_group()], [-vk.gamma_g2, -vk.delta_g2, proof.b]);
    let alpha_beta = ark_bn254::Bn254::final_exponentiation(ark_bn254::Bn254::multi_miller_loop([vk.alpha_g1.into_group()], [-vk.beta_g2])).unwrap().0.inverse().unwrap();
    let f = ark_bn254::Bn254::final_exponentiation(qap).unwrap().0;
    return f == alpha_beta;
}

pub fn groth16_verifier_circuit(public: Wires, proof_a: Wires, proof_b: Wires, proof_c: Wires, vk: ark_groth16::VerifyingKey<ark_bn254::Bn254>) -> (Wirex, usize) {
    let mut gate_count = 0;
    let (msm_temp, gc) = (wires_set_from_g1p(ark_bn254::G1Projective::msm(&vec![vk.gamma_abc_g1[1]], &vec![fr_from_wires(public.clone())]).unwrap()), 696000000);
    // let (msm_temp, gc) = G1Projective::msm_with_constant_bases_evaluate::<10>(vec![public], vec![vk.gamma_abc_g1[1].into_group()]);
    gate_count += gc;
    let (msm, gc) = G1Projective::add_evaluate(msm_temp, wires_set_from_g1p(vk.gamma_abc_g1[0].into_group()));
    gate_count += gc;

    let (f, gc) = multi_miller_loop_groth16_circuit_evaluate(msm, proof_c, proof_a, -vk.gamma_g2, -vk.delta_g2, proof_b);
    gate_count += gc;

    let alpha_beta = ark_bn254::Bn254::final_exponentiation(ark_bn254::Bn254::multi_miller_loop([vk.alpha_g1.into_group()], [-vk.beta_g2])).unwrap().0.inverse().unwrap();
    let f = wires_set_from_fq12(ark_bn254::Bn254::final_exponentiation(MillerLoopOutput(fq12_from_wires(f))).unwrap().0);

    let (result, gc) = fq12_equal_constant_evaluate(f, alpha_beta);
    gate_count += gc;
    (result[0].clone(), gate_count)
}

#[cfg(test)]
mod tests {
    use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_groth16::Groth16;
    use ark_std::{rand::{RngCore, SeedableRng}, test_rng};
    use ark_ff::{PrimeField, UniformRand};
    use ark_relations::lc;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    use crate::circuits::bn254::utils::{wires_set_from_fr, wires_set_from_g2a};
    use super::*;

    #[derive(Copy)]
    struct DummyCircuit<F: PrimeField> {
        pub a: Option<F>,
        pub b: Option<F>,
        pub num_variables: usize,
        pub num_constraints: usize,
    }

    impl<F: PrimeField> Clone for DummyCircuit<F> {
        fn clone(&self) -> Self {
            DummyCircuit {
                a: self.a,
                b: self.b,
                num_variables: self.num_variables,
                num_constraints: self.num_constraints,
            }
        }
    }

    impl<F: PrimeField> ConstraintSynthesizer<F> for DummyCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c = cs.new_input_variable(|| {
                let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                Ok(a * b)
            })?;

            for _ in 0..(self.num_variables - 3) {
                let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            }

            for _ in 0..self.num_constraints - 1 {
                cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
            }

            cs.enforce_constraint(lc!(), lc!(), lc!())?;

            Ok(())
        }
    }

    #[test]
    fn test_groth16_verifier() {
        let k = 6;
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let circuit = DummyCircuit::<<ark_bn254::Bn254 as Pairing>::ScalarField> {
            a: Some(<ark_bn254::Bn254 as Pairing>::ScalarField::rand(&mut rng)),
            b: Some(<ark_bn254::Bn254 as Pairing>::ScalarField::rand(&mut rng)),
            num_variables: 10,
            num_constraints: 1 << k,
        };
        let (pk, vk) = Groth16::<ark_bn254::Bn254>::setup(circuit, &mut rng).unwrap();

        let c = circuit.a.unwrap() * circuit.b.unwrap();

        let proof = Groth16::<ark_bn254::Bn254>::prove(&pk, circuit, &mut rng).unwrap();
        assert!(groth16_verifier(vec![c], proof, vk));
    }

    #[test]
    fn test_groth16_verifier_circuit() {
        let k = 6;
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let circuit = DummyCircuit::<<ark_bn254::Bn254 as Pairing>::ScalarField> {
            a: Some(<ark_bn254::Bn254 as Pairing>::ScalarField::rand(&mut rng)),
            b: Some(<ark_bn254::Bn254 as Pairing>::ScalarField::rand(&mut rng)),
            num_variables: 10,
            num_constraints: 1 << k,
        };
        let (pk, vk) = Groth16::<ark_bn254::Bn254>::setup(circuit, &mut rng).unwrap();

        let c = circuit.a.unwrap() * circuit.b.unwrap();

        let proof = Groth16::<ark_bn254::Bn254>::prove(&pk, circuit, &mut rng).unwrap();
        assert!(groth16_verifier(vec![c], proof.clone(), vk.clone()));

        println!("proof is correct in rust");

        let public = wires_set_from_fr(c);
        let proof_a = wires_set_from_g1p(proof.a.into_group());
        let proof_b = wires_set_from_g2a(proof.b);
        let proof_c = wires_set_from_g1p(proof.c.into_group());

        let (result, gate_count) = groth16_verifier_circuit(public, proof_a, proof_b, proof_c, vk);
        println!("gate_count: {:?}", gate_count);
        assert!(result.borrow().get_value());
    }
}
