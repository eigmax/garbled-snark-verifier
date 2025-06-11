use ark_ec::{bn::BnConfig, short_weierstrass::SWCurveConfig, CurveGroup};
use ark_ff::{AdditiveGroup, Field};
use crate::circuits::bn254::{fp254impl::Fp254Impl, fq::Fq};

pub fn double_in_place(r: &mut ark_bn254::G2Projective, half: ark_bn254::Fq) -> (ark_bn254::Fq2, ark_bn254::Fq2, ark_bn254::Fq2) {
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

pub fn mul_by_char(r: ark_bn254::G2Affine) -> ark_bn254::G2Affine {
    let mut s = r;
    s.x.frobenius_map_in_place(1);
    s.x *= &ark_bn254::Config::TWIST_MUL_BY_Q_X;
    s.y.frobenius_map_in_place(1);
    s.y *= &ark_bn254::Config::TWIST_MUL_BY_Q_Y;
    s
}

pub fn ell_coeffs(q: ark_bn254::G2Projective) -> Vec<(ark_bn254::Fq2, ark_bn254::Fq2, ark_bn254::Fq2)> {
    let half = ark_bn254::Fq::from(Fq::half_modulus());
    let q_affine = q.into_affine();
    let mut ellc = Vec::new();
    let mut r = ark_bn254::G2Projective {
        x: q_affine.x,
        y: q_affine.y,
        z: ark_bn254::Fq2::ONE,
    };
    let neg_q = -q_affine;
    for bit in ark_bn254::Config::ATE_LOOP_COUNT.iter().rev().skip(1) {
        ellc.push(double_in_place(&mut r, half));

        match bit {
            1 => {
                ellc.push(add_in_place(&mut r, &q_affine));
            },
            -1 => {
                ellc.push(add_in_place(&mut r, &neg_q));
            },
            _ => {},
        }
    }
    let q1 = mul_by_char(q_affine);
    let mut q2 = mul_by_char(q1);
    q2.y = -q2.y;
    ellc.push(add_in_place(&mut r, &q1));
    ellc.push(add_in_place(&mut r, &q2));
    ellc
}

pub fn ell(f: &mut ark_bn254::Fq12, coeffs: (ark_bn254::Fq2, ark_bn254::Fq2, ark_bn254::Fq2), p: ark_bn254::G1Projective) {
    let mut c0 = coeffs.0;
    let mut c1 = coeffs.1;
    let c2 = coeffs.2;

    c0.mul_assign_by_fp(&p.y);
    c1.mul_assign_by_fp(&p.x);
    f.mul_by_034(&c0, &c1, &c2);
}

pub fn miller_loop(p: ark_bn254::G1Projective, q: ark_bn254::G2Projective) -> ark_bn254::Fq12 {
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

#[cfg(test)]
mod tests {
    use ark_ff::UniformRand;
    use ark_std::rand::SeedableRng;
    use ark_ec::pairing::Pairing;
    use rand_chacha::ChaCha20Rng;
    use super::*;

    #[test]
    fn test_miller_loop() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        let p = ark_bn254::G1Projective::rand(&mut prng);
        let q = ark_bn254::G2Projective::rand(&mut prng);

        let c = ark_bn254::Bn254::multi_miller_loop([p], [q]).0;
        let d = miller_loop(p, q);
        assert_eq!(c, d);
    }
}
