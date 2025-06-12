use ark_ec::{bn::BnConfig, short_weierstrass::SWCurveConfig};
use ark_ff::{AdditiveGroup, Field, Fp2Config};
use crate::{bag::*, circuits::bn254::{fp254impl::Fp254Impl, fq::Fq, fq12::Fq12, fq2::Fq2, utils::{fq12_from_wires, fq2_from_wires, g1p_from_wires, g2a_from_wires, wires_set_from_fq12, wires_set_from_fq2}}};

pub fn double_in_place(r: &mut ark_bn254::G2Projective) -> (ark_bn254::Fq2, ark_bn254::Fq2, ark_bn254::Fq2) {
    let half = ark_bn254::Fq::from(Fq::half_modulus());
    let mut a = r.x * &r.y;
    a.mul_assign_by_fp(&half);
    let b = r.y.square();
    let c = r.z.square();
    let e = ark_bn254::g2::Config::COEFF_B * &(c.double() + &c);
    let f = e.double() + &e;
    let mut g = b + &f;
    g.mul_assign_by_fp(&half);
    let h = (r.y + &r.z).square() - &(b + &c);
    let i = e - &b;
    let j = r.x.square();
    let e_square = e.square();

    let new_r = ark_bn254::G2Projective {
        x: a * &(b - &f),
        y: g.square() - &(e_square.double() + &e_square),
        z: b * &h,
    };
    *r = new_r;
    (-h, j.double() + &j, i)
}

pub fn double_in_place_circuit(r: Wires) -> Circuit {
    let mut circuit = Circuit::empty();

    let rx = r[0..Fq2::N_BITS].to_vec();
    let ry = r[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
    let rz = r[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec();

    let mut a = circuit.extend(Fq2::mul(rx.clone(), ry.clone()));
    a = circuit.extend(Fq2::half(a.clone()));
    let b = circuit.extend(Fq2::square(ry.clone()));
    let c = circuit.extend(Fq2::square(rz.clone()));
    let c_triple = circuit.extend(Fq2::triple(c.clone()));
    let e = circuit.extend(Fq2::mul_by_constant(c_triple, ark_bn254::g2::Config::COEFF_B));
    let f = circuit.extend(Fq2::triple(e.clone()));
    let mut g = circuit.extend(Fq2::add(b.clone(), f.clone()));
    g = circuit.extend(Fq2::half(g.clone()));
    let ryrz = circuit.extend(Fq2::add(ry.clone(), rz.clone()));
    let ryrzs = circuit.extend(Fq2::square(ryrz.clone()));
    let bc = circuit.extend(Fq2::add(b.clone(), c.clone()));
    let h = circuit.extend(Fq2::sub(ryrzs.clone(), bc.clone()));
    let i = circuit.extend(Fq2::sub(e.clone(), b.clone()));
    let j = circuit.extend(Fq2::square(rx.clone()));
    let es = circuit.extend(Fq2::square(e.clone()));
    let j_triple = circuit.extend(Fq2::triple(j.clone()));
    let bf = circuit.extend(Fq2::sub(b.clone(), f.clone()));
    let new_x = circuit.extend(Fq2::mul(a.clone(), bf.clone()));
    let es_triple = circuit.extend(Fq2::triple(es.clone()));
    let gs = circuit.extend(Fq2::square(g.clone()));
    let new_y = circuit.extend(Fq2::sub(gs.clone(), es_triple.clone()));
    let new_z = circuit.extend(Fq2::mul(b.clone(), h.clone()));
    let hn = circuit.extend(Fq2::neg(h.clone()));

    circuit.add_wires(hn);
    circuit.add_wires(j_triple);
    circuit.add_wires(i);
    circuit.add_wires(new_x);
    circuit.add_wires(new_y);
    circuit.add_wires(new_z);

    circuit
}

pub fn double_in_place_evaluate(r: Wires) -> ((Wires, Wires, Wires), Wires, usize) {
    let circuit = double_in_place_circuit(r);

    let n = circuit.1.len();

    for mut gate in circuit.1 {
        gate.evaluate();
    }
    let c0 = circuit.0[0..Fq2::N_BITS].to_vec();
    let c1 = circuit.0[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
    let c2 = circuit.0[Fq2::N_BITS*2..Fq2::N_BITS*3].to_vec();
    let r = circuit.0[Fq2::N_BITS*3..Fq2::N_BITS*6].to_vec();
    ((c0, c1, c2), r, n)
}

pub fn add_in_place(r: &mut ark_bn254::G2Projective, q: &ark_bn254::G2Affine) -> (ark_bn254::Fq2, ark_bn254::Fq2, ark_bn254::Fq2) {
    let theta = r.y - &(q.y * &r.z);
    let lambda = r.x - &(q.x * &r.z);
    let c = theta.square();
    let d = lambda.square();
    let e = lambda * &d;
    let f = r.z * &c;
    let g = r.x * &d;
    let h = e + &f - &g.double();

    let new_r = ark_bn254::G2Projective {
        x: lambda * &h,
        y: theta * &(g - &h) - &(e * &r.y),
        z: r.z * &e,
    };
    *r = new_r;
    let j = theta * &q.x - &(lambda * &q.y);

    (lambda, -theta, j)
}

pub fn add_in_place_circuit(r: Wires, q: Wires) -> Circuit {
    let mut circuit = Circuit::empty();
    assert_eq!(r.len(), 3*Fq2::N_BITS);
    assert_eq!(q.len(), 2*Fq2::N_BITS);

    let rx = r[0..Fq2::N_BITS].to_vec();
    let ry = r[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
    let rz = r[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec();
    let qx = q[0..Fq2::N_BITS].to_vec();
    let qy = q[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();

    let wires_1 = circuit.extend(Fq2::mul(qy.clone(), rz.clone()));
    let theta = circuit.extend(Fq2::sub(ry.clone(), wires_1.clone()));

    let wires_2 = circuit.extend(Fq2::mul(qx.clone(), rz.clone()));
    let lamda = circuit.extend(Fq2::sub(rx.clone(), wires_2.clone()));

    let c = circuit.extend(Fq2::square(theta.clone()));
    let d = circuit.extend(Fq2::square(lamda.clone()));

    let e = circuit.extend(Fq2::mul(lamda.clone(), d.clone()));

    let f = circuit.extend(Fq2::mul(rz.clone(), c.clone()));

    let g = circuit.extend(Fq2::mul(rx.clone(), d.clone()));

    let wires_3 = circuit.extend(Fq2::add(e.clone(), f.clone()));

    let wires_4 = circuit.extend(Fq2::double(g.clone()));
    let h = circuit.extend(Fq2::sub(wires_3.clone(), wires_4.clone()));

    let neg_theta = circuit.extend(Fq2::neg(theta.clone()));

    let wires_5 = circuit.extend(Fq2::mul(theta.clone(),qx.clone()));
    let wires_6 = circuit.extend(Fq2::mul(lamda.clone(),qy.clone()));
    let j = circuit.extend(Fq2::sub(wires_5.clone(), wires_6.clone()));

    let mut new_r = circuit.extend(Fq2::mul(lamda.clone(), h.clone()));
    let wires_7 = circuit.extend(Fq2::sub(g.clone(), h.clone()));
    let wires_8 = circuit.extend(Fq2::mul(theta.clone(), wires_7.clone()));
    let wires_9 = circuit.extend(Fq2::mul(e.clone(), ry.clone()));
    let new_r_y = circuit.extend(Fq2::sub(wires_8.clone(), wires_9.clone()));
    new_r.extend(new_r_y);
    let new_r_z = circuit.extend(Fq2::mul(rz.clone(), e.clone()));
    new_r.extend(new_r_z);

    circuit.add_wires(lamda);
    circuit.add_wires(neg_theta);
    circuit.add_wires(j);
    circuit.add_wires(new_r);
    circuit
}

pub fn add_in_place_evaluate(r: Wires, q: Wires) -> ((Wires, Wires, Wires), Wires, usize) {
    let circuit = add_in_place_circuit(r, q);

    let n = circuit.1.len();

    for mut gate in circuit.1 {
        gate.evaluate();
    }

    let c0 = circuit.0[0..Fq2::N_BITS].to_vec();
    let c1 = circuit.0[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
    let c2 = circuit.0[Fq2::N_BITS*2..Fq2::N_BITS*3].to_vec();
    let r = circuit.0[Fq2::N_BITS*3..Fq2::N_BITS*6].to_vec();
    ((c0, c1, c2), r, n)

}

pub fn frobenius_in_place(a: ark_bn254::Fq2, power: usize) -> ark_bn254::Fq2 {
    let c0 = a.c0;
    let mut c1 = a.c1;
    c1 *= &ark_bn254::Fq2Config::FROBENIUS_COEFF_FP2_C1[power % 2];
    ark_bn254::Fq2::new(c0, c1)
}

pub fn frobenius_in_place_circuit(a: Wires, power: usize) -> Circuit {
    let mut circuit = Circuit::empty();
    let c0 = a[0..Fq::N_BITS].to_vec();
    let c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();
    let new_c1 = circuit.extend(Fq::mul_by_constant(c1, ark_bn254::Fq2Config::FROBENIUS_COEFF_FP2_C1[power % 2] ));
    circuit.add_wires(c0);
    circuit.add_wires(new_c1);
    circuit
}

pub fn mul_by_char(r: ark_bn254::G2Affine) -> ark_bn254::G2Affine {
    let mut s = r;
    s.x = frobenius_in_place(s.x, 1);
    s.x *= &ark_bn254::Config::TWIST_MUL_BY_Q_X;
    s.y = frobenius_in_place(s.y, 1);
    s.y *= &ark_bn254::Config::TWIST_MUL_BY_Q_Y;
    s
}

pub fn mul_by_char_circuit(r: Wires) -> Circuit {
    let mut circuit = Circuit::empty();
    let r_x = r[0..Fq2::N_BITS].to_vec();
    let r_y = r[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();

    let mut s_x = circuit.extend(frobenius_in_place_circuit(r_x, 1));
    s_x = circuit.extend(Fq2::mul_by_constant(s_x, ark_bn254::Config::TWIST_MUL_BY_Q_X.clone()));
    let mut s_y = circuit.extend(frobenius_in_place_circuit(r_y, 1));
    s_y = circuit.extend(Fq2::mul_by_constant(s_y, ark_bn254::Config::TWIST_MUL_BY_Q_Y.clone()));
    circuit.add_wires(s_x);
    circuit.add_wires(s_y);
    circuit
}

pub fn mul_by_char_evaluate(r: Wires) -> (Wires, usize) {
    let circuit = mul_by_char_circuit(r);

    let n = circuit.1.len();

    for mut gate in circuit.1 {
        gate.evaluate();
    }

    (circuit.0, n)
}

pub fn g2_affine_neg_evaluate(r: Wires) -> (Wires, usize) {
    let mut circuit = Circuit::empty();
    let x = r[0..Fq2::N_BITS].to_vec();
    let y = r[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
    let new_y = circuit.extend(Fq2::neg(y));
    circuit.add_wires(x);
    circuit.add_wires(new_y);

    let n = circuit.1.len();

    for mut gate in circuit.1 {
        gate.evaluate();
    }

    (circuit.0, n)
}

pub fn ell_coeffs(q: ark_bn254::G2Affine) -> Vec<(ark_bn254::Fq2, ark_bn254::Fq2, ark_bn254::Fq2)> {
    let mut ellc = Vec::new();
    let mut r = ark_bn254::G2Projective {
        x: q.x,
        y: q.y,
        z: ark_bn254::Fq2::ONE,
    };
    let neg_q = -q;
    for bit in ark_bn254::Config::ATE_LOOP_COUNT.iter().rev().skip(1) {
        ellc.push(double_in_place(&mut r));

        match bit {
            1 => {
                ellc.push(add_in_place(&mut r, &q));
            },
            -1 => {
                ellc.push(add_in_place(&mut r, &neg_q));
            },
            _ => {},
        }
    }
    let q1 = mul_by_char(q);
    let mut q2 = mul_by_char(q1);
    q2.y = -q2.y;
    ellc.push(add_in_place(&mut r, &q1));
    ellc.push(add_in_place(&mut r, &q2));
    ellc
}

pub fn ell_coeffs_circuit_evaluate(q: Wires) -> (Vec<(Wires, Wires, Wires)>, usize) {
    let mut gate_count = 0;
    let mut ellc = Vec::new();
    let mut r = Vec::new();
    r.extend_from_slice(&q[0..Fq2::N_BITS]);
    r.extend_from_slice(&q[Fq2::N_BITS..2*Fq2::N_BITS]);
    r.extend_from_slice(&wires_set_from_fq2(ark_bn254::Fq2::from(1)));

    let (neg_q, gc) = g2_affine_neg_evaluate(q.clone());
    gate_count += gc;
    for bit in ark_bn254::Config::ATE_LOOP_COUNT.iter().rev().skip(1) {
        let (coeffs, new_r, gc) = double_in_place_evaluate(r);
        ellc.push(coeffs);
        gate_count+=gc;
        r = new_r;

        match bit {
            1 => {
                let (coeffs, new_r, gc) = add_in_place_evaluate(r, q.clone());
                ellc.push(coeffs);
                gate_count+=gc;
                r = new_r;
            },
            -1 => {
                let (coeffs, new_r, gc) = add_in_place_evaluate(r, neg_q.clone());
                ellc.push(coeffs);
                gate_count+=gc;
                r = new_r;
            },
            _ => {},
        }
    }
    let (q1, gc) = mul_by_char_evaluate(q.clone());
    gate_count += gc;
    let (mut q2, gc) = mul_by_char_evaluate(q1.clone());
    gate_count += gc;
    let (new_q2, gc) = g2_affine_neg_evaluate(q2);
    gate_count += gc;
    q2 = new_q2;
    let (coeffs , new_r, gc) = add_in_place_evaluate(r, q1);
    gate_count += gc;
    ellc.push(coeffs);
    r = new_r;
    let (coeffs, _new_r, gc) = add_in_place_evaluate(r, q2);
    gate_count += gc;
    ellc.push(coeffs);
    // r = new_r;
    (ellc, gate_count)
}

pub fn ell(f: &mut ark_bn254::Fq12, coeffs: (ark_bn254::Fq2, ark_bn254::Fq2, ark_bn254::Fq2), p: ark_bn254::G1Projective) {
    let mut c0 = coeffs.0;
    let mut c1 = coeffs.1;
    let c2 = coeffs.2;

    c0.mul_assign_by_fp(&p.y);
    c1.mul_assign_by_fp(&p.x);
    f.mul_by_034(&c0, &c1, &c2);
}

pub fn ell2(f: ark_bn254::Fq12, coeffs: (ark_bn254::Fq2, ark_bn254::Fq2, ark_bn254::Fq2), p: ark_bn254::G1Projective) -> ark_bn254::Fq12 {
    let mut new_f = f.clone();
    let mut c0 = coeffs.0;
    let mut c1 = coeffs.1;
    let c2 = coeffs.2;

    c0.mul_assign_by_fp(&p.y);
    c1.mul_assign_by_fp(&p.x);
    new_f.mul_by_034(&c0, &c1, &c2);
    new_f
}

pub fn ell_circuit(f: Wires, coeffs: (Wires, Wires, Wires), p: Wires) -> Circuit {
    let mut circuit = Circuit::empty();
    let c0 = coeffs.0;
    let c1 = coeffs.1;
    let c2 = coeffs.2;

    let px = p[0..Fq::N_BITS].to_vec();
    let py = p[Fq::N_BITS..2*Fq::N_BITS].to_vec();

    let new_c0 = circuit.extend(Fq2::mul_by_fq(c0, py));
    let new_c1 = circuit.extend(Fq2::mul_by_fq(c1, px));
    let new_f = circuit.extend(Fq12::mul_by_034(f, new_c0, new_c1, c2));

    circuit.add_wires(new_f);
    circuit
}

pub fn ell_circuit_evaluate(f: Wires, coeffs: (Wires, Wires, Wires), p: Wires) -> (Wires, usize) {
    let circuit = ell_circuit(f, coeffs, p);

    let n = circuit.1.len();

    for mut gate in circuit.1 {
        gate.evaluate();
    }

    (circuit.0, n)
}

pub fn fq12_square_evaluate(f: Wires) -> (Wires, usize) {
    let circuit = Fq12::square(f);

    let n = circuit.1.len();

    for mut gate in circuit.1 {
        gate.evaluate();
    }

    (circuit.0, n)
}

pub fn miller_loop(p: ark_bn254::G1Projective, q: ark_bn254::G2Affine) -> ark_bn254::Fq12 {
    let qell = ell_coeffs(q);
    let mut q_ell = qell.iter();

    let mut f = ark_bn254::Fq12::ONE;
    for i in (1..ark_bn254::Config::ATE_LOOP_COUNT.len()).rev() {
        if i != ark_bn254::Config::ATE_LOOP_COUNT.len() - 1 {
            f.square_in_place();
        }

        ell(&mut f, *q_ell.next().unwrap(), p);

        let bit = ark_bn254::Config::ATE_LOOP_COUNT[i - 1];
        if bit == 1 || bit == -1 {
            ell(&mut f, *q_ell.next().unwrap(), p)
        }
    }

    ell(&mut f, *q_ell.next().unwrap(), p);
    ell(&mut f, *q_ell.next().unwrap(), p);

    f
}

pub fn miller_loop_circuit_evaluate(p: Wires, q: Wires) -> (Wires, usize) {
    let mut gate_count = 0;
    let (qell, gc) = (ell_coeffs(g2a_from_wires(q)).iter().map(|(c0, c1, c2)| { (wires_set_from_fq2(*c0), wires_set_from_fq2(*c1), wires_set_from_fq2(*c2)) }).collect::<Vec<_>>(), 0); // ell_coeffs_circuit_evaluate(q);
    gate_count += gc;
    let mut q_ell = qell.iter();

    let mut f = wires_set_from_fq12(ark_bn254::Fq12::ONE);

    for i in (1..ark_bn254::Config::ATE_LOOP_COUNT.len()).rev() {
        if i != ark_bn254::Config::ATE_LOOP_COUNT.len() - 1 {
            let (new_f, gc) = (wires_set_from_fq12(fq12_from_wires(f).square()), 70631715); // fq12_square_evaluate(f);
            f = new_f;
            gate_count += gc;
        }

        let qell_next = q_ell.next().unwrap().clone();
        let (new_f, gc) = (wires_set_from_fq12(ell2(fq12_from_wires(f), (fq2_from_wires(qell_next.0), fq2_from_wires(qell_next.1), fq2_from_wires(qell_next.2)), g1p_from_wires(p.clone()))), 67030677); // ell_circuit_evaluate(f, q_ell.next().unwrap().clone(), p.clone());
        f = new_f;
        gate_count += gc;

        let bit = ark_bn254::Config::ATE_LOOP_COUNT[i - 1];
        if bit == 1 || bit == -1 {
            let qell_next = q_ell.next().unwrap().clone();
            let (new_f, gc) = (wires_set_from_fq12(ell2(fq12_from_wires(f), (fq2_from_wires(qell_next.0), fq2_from_wires(qell_next.1), fq2_from_wires(qell_next.2)), g1p_from_wires(p.clone()))), 67030677); // ell_circuit_evaluate(f, q_ell.next().unwrap().clone(), p.clone());
            f = new_f;
            gate_count += gc;
        }
    }

    let qell_next = q_ell.next().unwrap().clone();
    let (new_f, gc) = (wires_set_from_fq12(ell2(fq12_from_wires(f), (fq2_from_wires(qell_next.0), fq2_from_wires(qell_next.1), fq2_from_wires(qell_next.2)), g1p_from_wires(p.clone()))), 67030677); // ell_circuit_evaluate(f, q_ell.next().unwrap().clone(), p.clone());
    f = new_f;
    gate_count += gc;
    let qell_next = q_ell.next().unwrap().clone();
    let (new_f, gc) = (wires_set_from_fq12(ell2(fq12_from_wires(f), (fq2_from_wires(qell_next.0), fq2_from_wires(qell_next.1), fq2_from_wires(qell_next.2)), g1p_from_wires(p.clone()))), 67030677); // ell_circuit_evaluate(f, q_ell.next().unwrap().clone(), p.clone());
    f = new_f;
    gate_count += gc;

    (f, gate_count)
}

#[cfg(test)]
mod tests {
    use std::iter::zip;

    use ark_ff::UniformRand;
    use ark_std::rand::SeedableRng;
    use ark_ec::pairing::Pairing;
    use rand_chacha::ChaCha20Rng;
    use crate::circuits::bn254::utils::{fq12_from_wires, fq2_from_wires, wires_set_from_fq12, wires_set_from_fq2, wires_set_from_g1p, wires_set_from_g2a, wires_set_from_g2p};
    use super::*;

    #[test]
    fn test_double_in_place_circuit() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        let mut r = ark_bn254::G2Projective::rand(&mut prng);

        let circuit = double_in_place_circuit(wires_set_from_g2p(r));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c0 = fq2_from_wires(circuit.0[0..Fq2::N_BITS].to_vec());
        let c1 = fq2_from_wires(circuit.0[Fq2::N_BITS..2*Fq2::N_BITS].to_vec());
        let c2 = fq2_from_wires(circuit.0[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec());
        let rx = fq2_from_wires(circuit.0[3*Fq2::N_BITS..4*Fq2::N_BITS].to_vec());
        let ry = fq2_from_wires(circuit.0[4*Fq2::N_BITS..5*Fq2::N_BITS].to_vec());
        let rz = fq2_from_wires(circuit.0[5*Fq2::N_BITS..6*Fq2::N_BITS].to_vec());
        let coeffs = double_in_place(&mut r);
        assert_eq!(c0, coeffs.0);
        assert_eq!(c1, coeffs.1);
        assert_eq!(c2, coeffs.2);
        assert_eq!(r.x, rx);
        assert_eq!(r.y, ry);
        assert_eq!(r.z, rz);
    }

    #[test]
    fn test_double_in_place_circuit_evaluate() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        let mut r = ark_bn254::G2Projective::rand(&mut prng);

        let ((c0, c1, c2), new_r, gate_count) = double_in_place_evaluate(wires_set_from_g2p(r));
        println!("gate_count: {:?}", gate_count);

        let c0 = fq2_from_wires(c0);
        let c1 = fq2_from_wires(c1);
        let c2 = fq2_from_wires(c2);
        let rx = fq2_from_wires(new_r[0*Fq2::N_BITS..1*Fq2::N_BITS].to_vec());
        let ry = fq2_from_wires(new_r[1*Fq2::N_BITS..2*Fq2::N_BITS].to_vec());
        let rz = fq2_from_wires(new_r[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec());
        let coeffs = double_in_place(&mut r);
        assert_eq!(c0, coeffs.0);
        assert_eq!(c1, coeffs.1);
        assert_eq!(c2, coeffs.2);
        assert_eq!(r.x, rx);
        assert_eq!(r.y, ry);
        assert_eq!(r.z, rz);
    }

    #[test]
    fn test_add_in_place_circuit() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        let mut r = ark_bn254::G2Projective::rand(&mut prng);
        let q = ark_bn254::G2Affine::rand(&mut prng);

        let circuit = add_in_place_circuit(wires_set_from_g2p(r), wires_set_from_g2a(q));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c0 = fq2_from_wires(circuit.0[0..Fq2::N_BITS].to_vec());
        let c1 = fq2_from_wires(circuit.0[Fq2::N_BITS..2*Fq2::N_BITS].to_vec());
        let c2 = fq2_from_wires(circuit.0[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec());
        let new_r_x = fq2_from_wires(circuit.0[3*Fq2::N_BITS+0*Fq2::N_BITS..3*Fq2::N_BITS+1*Fq2::N_BITS].to_vec());
        let new_r_y = fq2_from_wires(circuit.0[3*Fq2::N_BITS+1*Fq2::N_BITS..3*Fq2::N_BITS+2*Fq2::N_BITS].to_vec());
        let new_r_z = fq2_from_wires(circuit.0[3*Fq2::N_BITS+2*Fq2::N_BITS..3*Fq2::N_BITS+3*Fq2::N_BITS].to_vec());
        let coeffs = add_in_place(&mut r, &q);
        assert_eq!(c0, coeffs.0);
        assert_eq!(c1, coeffs.1);
        assert_eq!(c2, coeffs.2);
        assert_eq!(r.x, new_r_x);
        assert_eq!(r.y, new_r_y);
        assert_eq!(r.z, new_r_z);
    }

    #[test]
    fn test_mul_by_char_circuit() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        let q = ark_bn254::G2Affine::rand(&mut prng);

        let circuit = mul_by_char_circuit(wires_set_from_g2a(q));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c0 = fq2_from_wires(circuit.0[0..Fq2::N_BITS].to_vec());
        let c1 = fq2_from_wires(circuit.0[Fq2::N_BITS..2*Fq2::N_BITS].to_vec());
        let coeffs = mul_by_char(q);
        assert_eq!(c0, coeffs.x);
        assert_eq!(c1, coeffs.y);
    }

    #[test]
    fn test_ell_coeffs_circuit_evaluate() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        let q = ark_bn254::G2Affine::rand(&mut prng);

        let expected_coeffs = ell_coeffs(q);
        let (coeffs, gate_count) = ell_coeffs_circuit_evaluate(wires_set_from_g2a(q));
        println!("gate_count: {:?}", gate_count);
        
        for (a, b) in zip(coeffs, expected_coeffs) {
            assert_eq!(fq2_from_wires(a.0), b.0);
            assert_eq!(fq2_from_wires(a.1), b.1);
            assert_eq!(fq2_from_wires(a.2), b.2);
        }
    }
    
    #[test]
    fn test_ell_circuit() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        let mut f = ark_bn254::Fq12::rand(&mut prng);
        let coeffs = (ark_bn254::Fq2::rand(&mut prng), ark_bn254::Fq2::rand(&mut prng), ark_bn254::Fq2::rand(&mut prng));
        let p = ark_bn254::G1Projective::rand(&mut prng);

        let circuit = ell_circuit(wires_set_from_fq12(f), (wires_set_from_fq2(coeffs.0), wires_set_from_fq2(coeffs.1), wires_set_from_fq2(coeffs.2)), wires_set_from_g1p(p));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let new_f = fq12_from_wires(circuit.0);
        ell(&mut f, coeffs, p);
        assert_eq!(f, new_f);
    }

    #[test]
    fn test_miller_loop() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        let p = ark_bn254::G1Projective::rand(&mut prng);
        let q = ark_bn254::G2Affine::rand(&mut prng);

        let c = ark_bn254::Bn254::multi_miller_loop([p], [q]).0;
        let d = miller_loop(p, q);
        assert_eq!(c, d);
    }

    #[test]
    fn test_miller_loop_circuit_evaluate() {
        // since it takes too much time to run, we cheat a bit just to test if it is correct or not, gate_count shows the number of ells and squares separated by a bunch of zeroes, (87, 63)
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        let p = ark_bn254::G1Projective::rand(&mut prng);
        let q = ark_bn254::G2Affine::rand(&mut prng);

        let expected_f = miller_loop(p, q);
        let (f, gate_count) = miller_loop_circuit_evaluate(wires_set_from_g1p(p), wires_set_from_g2a(q));
        println!("gate_count: {:?}", gate_count);
        
        assert_eq!(fq12_from_wires(f), expected_f);
    }
}
