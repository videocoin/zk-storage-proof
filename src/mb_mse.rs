#![allow(unused_imports)]
#![allow(unused_variables)]
extern crate bellperson;
extern crate paired;
extern crate pbr;
extern crate rand;
use bellperson::{Circuit, ConstraintSystem, SynthesisError};
use paired::{Engine};
use paired::bls12_381::{Bls12, Fr};

use ff::Field;
use ff::PrimeField;
use fil_sapling_crypto::circuit::{boolean, multipack, num, pedersen_hash};
use storage_proofs::fr32::fr_into_bytes;
use rand::{Rng, SeedableRng, XorShiftRng};
use std::sync::{Arc, RwLock};
use super::pixel;

// We're going to use the Groth16 proving system.
use self::bellperson::groth16::{
    Proof,
    generate_random_parameters,
    prepare_verifying_key,
    create_random_proof,
    verify_proof,
};

#[derive(Clone)]
pub struct Mse<E: Engine> {
    pub srcPixels: Vec<Option<E::Fr>>,
	pub dstPixels: Vec<Option<E::Fr>>
}

impl <E: Engine> Circuit<E> for Mse<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self, 
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
		let mbSize = self.srcPixels.len();
	    let mut varvecSrc: Vec<_> = Vec::new();
		let mut varvecDst: Vec<_> = Vec::new();
		let mut varvecDiff: Vec<_> = Vec::new();
		let mut varvecDiffSq: Vec<_> = Vec::new();
		let mut varSum : pixel::AllocatedPixel<E>;
		let mut varMean : pixel::AllocatedPixel<E>;
		// Source pixel data
        for i in 0..mbSize {
            let mut cs = cs.namespace(|| format!("src {}", i));
            let value = self.srcPixels[i];
            let value_num = pixel::AllocatedPixel::alloc(cs.namespace(|| "value"), || {
                value.ok_or_else(|| SynthesisError::AssignmentMissing)
            })?;
			value_num.inputize(cs.namespace(|| "value num"))?;
			varvecSrc.push(value_num);
 		}
		// Destination pixel data	
        for i in 0..mbSize {
            let mut cs = cs.namespace(|| format!("dst {}", i));
            let value = self.srcPixels[i];
            let value_num = pixel::AllocatedPixel::alloc(cs.namespace(|| "value"), || {
                value.ok_or_else(|| SynthesisError::AssignmentMissing)
            })?;
			value_num.inputize(cs.namespace(|| "value num"))?;
			varvecDst.push(value_num);
		}
		// Difference
        for i in 0..mbSize {
            let mut cs = cs.namespace(|| format!("diff {}", i));
            let value_num = sub(cs.namespace(|| "c^5 - k"), &varvecSrc[i], &varvecDst[i])?;

			varvecDiff.push(value_num);
 		}
		// square		
	    for i in 0..mbSize {
            let mut cs = cs.namespace(|| format!("diffsq {}", i));
            let value_num = varvecDiff[i].square(cs).unwrap();
			varvecDiffSq.push(value_num);
 		}		
		// sum squares		
	    {
			let value = self.srcPixels[0]; // TODO replace
            let value_num = pixel::AllocatedPixel::alloc(cs.namespace(|| "sum"), || {
                value.ok_or_else(|| SynthesisError::AssignmentMissing)
            })?;
            let res = sumVec(cs, || format!("sum"), &varvecDiffSq, &value_num);
			varSum = value_num;
 		}		
		// mean square error
	    {
			let value = self.srcPixels[0]; // TODO replace
            let value_num = pixel::AllocatedPixel::alloc(cs.namespace(|| "mean"), || {
                value.ok_or_else(|| SynthesisError::AssignmentMissing)
            })?;
            let res = meanVec(cs, || format!("sum"), &varSum, &value_num);
			varMean = value_num;
 		}		
		
        Ok(())
    }
}

/// Adds a constraint to CS, enforcing an equality relationship between the allocated numbers a and b.
///
/// a == b
pub fn equal<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &pixel::AllocatedPixel<E>,
    b: &pixel::AllocatedPixel<E>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    // a * 1 = b
    cs.enforce(
        annotation,
        |lc| lc + a.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + b.get_variable(),
    );
}

/// Adds a constraint to CS, enforcing a difference relationship between the allocated numbers a, b, and difference.
///
/// a - b = difference
pub fn difference<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &pixel::AllocatedPixel<E>,
    b: &pixel::AllocatedPixel<E>,
    difference: &pixel::AllocatedPixel<E>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    //    difference = a-b
    // => difference + b = a
    // => (difference + b) * 1 = a
    cs.enforce(
        annotation,
        |lc| lc + difference.get_variable() + b.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + a.get_variable(),
    );
}

// From storage-proofs/src/circuit/sloths.rs
fn sub<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    a: &pixel::AllocatedPixel<E>,
    b: &pixel::AllocatedPixel<E>,
) -> Result<pixel::AllocatedPixel<E>, SynthesisError> {
    let res = pixel::AllocatedPixel::alloc(cs.namespace(|| "sub num"), || {
        let mut tmp = a
            .get_value()
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        tmp.sub_assign(
            &b.get_value()
                .ok_or_else(|| SynthesisError::AssignmentMissing)?,
        );

        Ok(tmp)
    })?;

    // a - b = res
    difference(&mut cs, || "subtraction constraint", &a, &b, &res);

    Ok(res)
}

pub fn sumVec<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &Vec<pixel::AllocatedPixel<E>>,
    sum: &pixel::AllocatedPixel<E>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    cs.enforce(
        annotation,
        |mut lc| {for i in 1..a.len() {lc = lc + a[i].get_variable()} lc},
        |lc| lc + CS::one(),
        |lc| lc + sum.get_variable(),
    );
}

pub fn meanVec<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    sum: &pixel::AllocatedPixel<E>,
    mean: &pixel::AllocatedPixel<E>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    cs.enforce(
        annotation,
        |lc| lc + sum.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + mean.get_variable(),
    );
}

pub fn main(_srcPixel: Vec<u32>, _dstPixel: Vec<u32>){
    use paired::bls12_381::{Bls12, Fr};
    use rand::thread_rng;
    use bellperson::groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof,
    };
    
    let rng = &mut thread_rng();
 	let mbSize = 256;
     // Create an instance of circuit
	let tmpsrcPixels: Vec<Option<Fr>> = _srcPixel.iter().map(|x| Fr::from_str("7")).collect();
	let tmpdstPixels: Vec<Option<Fr>> = _dstPixel.iter().map(|x| Fr::from_str("7")).collect();

    let c = Mse::<Bls12> {
		srcPixels: tmpsrcPixels.clone(),
		dstPixels: tmpdstPixels.clone()
    };

    // Create parameters for our circuit
    let params = {
        let c = Mse::<Bls12> {
            srcPixels: tmpsrcPixels.clone(),
			dstPixels: tmpdstPixels.clone()
        };

        generate_random_parameters(c, rng).unwrap()
    };
    
    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");
    

    
    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(c, &params, rng).unwrap();
    let expected_inputs: Vec<Fr> = tmpsrcPixels.into_iter().map(|n| n.unwrap()).collect();  
    assert!(verify_proof(
        &pvk,
        &proof,
        &expected_inputs[..]
    ).unwrap());
}