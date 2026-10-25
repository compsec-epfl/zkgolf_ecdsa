#![allow(dead_code)]
use bellpepper_core::{
    ConstraintSystem, LinearCombination, SynthesisError,
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    test_cs::TestConstraintSystem,
};
use ff::{Field, PrimeField, PrimeFieldBits};
use halo2curves::secp256r1::Fp as Scalar;
use std::sync::atomic::{AtomicBool, Ordering};
#[path = "upstream/allocated_point.rs"]
pub mod allocated_point_file;
#[path = "upstream/constant_point.rs"]
pub mod constant_point_file;
#[path = "upstream/constraints_utils.rs"]
pub mod constraints_utils_file;
mod noir {
    pub mod synthesis {
        pub use crate::allocated_point_file as allocated_point;
        pub use crate::constant_point_file as constant_point;
        pub use crate::constraints_utils_file as constraints_utils;
    }
}
use noir::synthesis::{allocated_point::AllocatedPoint, constant_point::ConstantPoint};
static MALICIOUS: AtomicBool = AtomicBool::new(false);
fn audit_bits<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
    s: &AllocatedNum<F>,
    mut cs: CS,
) -> Result<Vec<Boolean>, SynthesisError> {
    if !MALICIOUS.load(Ordering::Relaxed) || s.get_value() != Some(F::ZERO) {
        return s.to_bits_le(cs);
    }
    let bits = (0..F::NUM_BITS as usize)
        .map(|i| {
            AllocatedBit::alloc(
                cs.namespace(|| format!("bit {}", i)),
                Some(F::char_le_bits()[i]),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut lc = LinearCombination::zero();
    let mut coeff = F::ONE;
    for b in &bits {
        lc = lc + (coeff, b.get_variable());
        coeff = coeff.double();
    }
    lc = lc - s.get_variable();
    cs.enforce(|| "unpacking constraint", |lc| lc, |lc| lc, |_| lc);
    Ok(bits.into_iter().map(Boolean::from).collect())
}
fn fe(s: &str) -> Scalar {
    let mut v = Scalar::ZERO;
    for c in s.chars() {
        v = v * Scalar::from(16) + Scalar::from(c.to_digit(16).unwrap() as u64)
    }
    v
}
fn generator() -> ConstantPoint<Scalar> {
    ConstantPoint::new(
        fe("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296"),
        fe("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5"),
    )
}
fn run(malicious: bool, fixed: bool) -> (TestConstraintSystem<Scalar>, AllocatedPoint<Scalar>) {
    MALICIOUS.store(malicious, Ordering::Relaxed);
    let mut cs = TestConstraintSystem::new();
    let base = generator();
    let s = AllocatedNum::alloc(cs.namespace(|| "scalar"), || Ok(Scalar::ZERO)).unwrap();
    let r = if fixed {
        AllocatedPoint::scalar_mul_fixed_base(cs.namespace(|| "mul"), &base, &s).unwrap()
    } else {
        let pt =
            AllocatedPoint::_alloc(cs.namespace(|| "base"), Some((base.x, base.y, false))).unwrap();
        pt.scalar_mul(cs.namespace(|| "mul"), &s).unwrap()
    };
    (cs, r)
}
fn main() {
    bits_cost();
    full_equation();
    for fixed in [false, true] {
        let (honest, h) = run(false, fixed);
        let (malicious, m) = run(true, fixed);
        assert!(honest.is_satisfied());
        assert!(malicious.is_satisfied());
        assert_eq!(honest.hash(), malicious.hash());
        assert_eq!(h.is_infinity.get_value(), Some(Scalar::ONE));
        assert_eq!(m.is_infinity.get_value(), Some(Scalar::ZERO));
        println!(
            "fixed={} rows={} same_constraint_hash={} honest_zero_is_infinity={:?} malicious_zero_is_infinity={:?} malicious_xy={:?},{:?}",
            fixed,
            honest.num_constraints(),
            honest.hash(),
            h.is_infinity.get_value().unwrap(),
            m.is_infinity.get_value().unwrap(),
            m.x.get_value(),
            m.y.get_value()
        );
    }
}

fn finite<CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    p: &AllocatedPoint<Scalar>,
) -> AllocatedPoint<Scalar> {
    AllocatedPoint {
        x: p.x.clone(),
        y: p.y.clone(),
        is_infinity: noir::synthesis::constraints_utils::alloc_zero(cs.namespace(|| "is_inf"))
            .unwrap(),
    }
}
fn full_equation() {
    MALICIOUS.store(true, Ordering::Relaxed);
    let mut cs = TestConstraintSystem::new();
    let g = generator();
    let r = g.double();
    let zero = AllocatedNum::alloc(cs.namespace(|| "s_inv"), || Ok(Scalar::ZERO)).unwrap();
    let e = AllocatedNum::alloc(cs.namespace(|| "digest"), || {
        Ok(fe(
            "a1057a6ab423ff6d0200604f75f86dfac5a35eed0b764e01248f9589585925",
        ))
    })
    .unwrap();
    let rx = AllocatedNum::alloc(cs.namespace(|| "rx"), || Ok(r.x)).unwrap();
    let ry = AllocatedNum::alloc(cs.namespace(|| "ry"), || Ok(r.y)).unwrap();
    let q = AllocatedPoint::_alloc(cs.namespace(|| "q"), Some((g.x, g.y, false))).unwrap();
    let sg = AllocatedPoint::scalar_mul_fixed_base(cs.namespace(|| "sG"), &g, &zero).unwrap();
    let sq = q.scalar_mul(cs.namespace(|| "sQ"), &zero).unwrap();
    let sg2 = finite(cs.namespace(|| "sgfinite"), &sg);
    let sq2 = finite(cs.namespace(|| "sqfinite"), &sq);
    let tsg = sg2.scalar_mul(cs.namespace(|| "tsG"), &e).unwrap();
    let rsq = sq2.scalar_mul(cs.namespace(|| "rsQ"), &rx).unwrap();
    let tsg2 = finite(cs.namespace(|| "tsgfinite"), &tsg);
    let rsq2 = finite(cs.namespace(|| "rsqfinite"), &rsq);
    let rhs = tsg2.add(cs.namespace(|| "finaladd"), &rsq2).unwrap();
    cs.enforce(
        || "equal_x",
        |lc| lc + rhs.x.get_variable() - rx.get_variable(),
        |lc| lc + TestConstraintSystem::<Scalar>::one(),
        |lc| lc,
    );
    cs.enforce(
        || "equal_y",
        |lc| lc + rhs.y.get_variable() - ry.get_variable(),
        |lc| lc + TestConstraintSystem::<Scalar>::one(),
        |lc| lc,
    );
    assert!(cs.is_satisfied(), "{:?}", cs.which_is_unsatisfied());
    println!(
        "FULL_FOUR_LADDER_EQUATION: accepted s_inv=0 with Q=G,R=2G,digest=a1057a6ab423ff6d0200604f75f86dfac5a35eed0b764e01248f9589585925,rows={},hash={}",
        cs.num_constraints(),
        cs.hash()
    );
}

fn bits_cost() {
    for strict in [false, true] {
        let mut cs = TestConstraintSystem::<Scalar>::new();
        let s = AllocatedNum::alloc(cs.namespace(|| "s"), || Ok(Scalar::ONE)).unwrap();
        if strict {
            s.to_bits_le_strict(cs.namespace(|| "bits")).unwrap();
        } else {
            s.to_bits_le(cs.namespace(|| "bits")).unwrap();
        }
        println!(
            "strict_decomposition={} rows={}",
            strict,
            cs.num_constraints()
        );
    }
}
