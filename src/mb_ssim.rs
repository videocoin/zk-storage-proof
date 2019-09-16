#![allow(unused_imports)]
#![allow(unused_variables)]
extern crate bellperson;
extern crate paired;
extern crate pbr;
extern crate rand;
use bellperson::{Circuit, ConstraintSystem, SynthesisError};
use paired::{Engine};
use paired::bls12_381::{Bls12, Fr, FrRepr};

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
pub struct Ssim<E: Engine> {
    pub srcPixels: Vec<Option<E::Fr>>,
	pub dstPixels: Vec<Option<E::Fr>>
}

impl <E: Engine> Circuit<E> for Ssim<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self, 
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
		let mbSize = self.srcPixels.len();
	    let mut varvec_src: Vec<_> = Vec::new();


		//let mut varvecDiffSqDst: Vec<_> = Vec::new();
		// Source pixel data
        for i in 0..mbSize {
            let mut cs = cs.namespace(|| format!("src {}", i));
            let value = self.srcPixels[i];
            let value_num = pixel::AllocatedPixel::alloc(cs.namespace(|| "value"), || {
                print!("We are called\n");
				value.ok_or_else(|| SynthesisError::AssignmentMissing)
            })?;
			value_num.inputize(cs.namespace(|| "value num"))?;
			varvec_src.push(value_num);
 		}

		let mut varvecDst: Vec<_> = Vec::new();
		// Destination pixel data. Auxiliary input	
        for i in 0..mbSize {
            let mut cs = cs.namespace(|| format!("dst {}", i));
            let value = self.srcPixels[i];
            let value_num = pixel::AllocatedPixel::alloc(cs.namespace(|| "value"), || {
                value.ok_or_else(|| SynthesisError::AssignmentMissing)
            })?;
			//value_num.inputize(cs.namespace(|| "value num"))?;
			varvecDst.push(value_num);
		}
			
		// mean source
		let varSumSrc = sumVec(cs, || format!("sum src"), &varvec_src).unwrap();
		let varMeanSrc = mean(cs, || format!("sum"), &varSumSrc, mbSize).unwrap();

		let varSumDst = sumVec(cs, || format!("sum src"), &varvecDst).unwrap();
		let varMeanDst = mean(cs, || format!("sum"), &varSumDst, mbSize).unwrap();
		
		let varVarianceSumSrc = variance(cs, || format!("var sum src"), &varvec_src, &varvec_src, &varMeanSrc, &varMeanSrc).unwrap();
		let varVarianceSumDst = variance(cs, || format!("var sum dst"), &varvecDst, &varvecDst, &varMeanDst, &varMeanDst).unwrap();
		let varCovarianceSum = variance(cs, || format!("covar sum"), &varvec_src, &varvecDst, &varMeanSrc, &varMeanDst).unwrap();
 		
		let varVarianceSrc = mean(cs, || format!("sum"), &varVarianceSumSrc, mbSize).unwrap();
		let varVarianceDst = mean(cs, || format!("sum"), &varVarianceSumDst, mbSize).unwrap();
		let varCovariance = mean(cs, || format!("sum"), &varCovarianceSum, mbSize).unwrap();
		
        Ok(())
    }
}

pub fn sumVec<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &Vec<pixel::AllocatedPixel<E>>
) -> Result<pixel::AllocatedPixel<E>, SynthesisError>
where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    let num_value = pixel::AllocatedPixel::alloc(cs.namespace(|| "sum"), || {
		let mbSize = a.len();
		let mut value = E::Fr::zero(); 
		for i in 0..mbSize {
			let pix = a[i].get_value();
			print!("Sample var={:?} val={:?}\n",  a[i].get_variable(), pix);
			value.add_assign(&pix.unwrap());
		}
        Ok(value)
    })?;
    sum_vec_enforce(cs, || "sum enforce", &a, &num_value);

	Ok(num_value)
}

pub fn sum_vec_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
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
        |mut lc| { 
	        for x in a.iter() {
		        lc = lc + x.get_variable()
			} 
			lc
		},
        |lc| lc + CS::one(),
        |lc| lc + sum.get_variable(),
    );
}

/// Adds a constraint to CS, enforcing a difference square relationship between the allocated numbers a, b, and difference.
/// (a - b)^2 = difference^2
pub fn meanEnforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &pixel::AllocatedPixel<E>,
    b: &pixel::AllocatedPixel<E>,
    num_elems: usize
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    //  a-b * a-b = diffsq

    cs.enforce(
        annotation,
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc + a.get_variable(),
    );
}

pub fn mean<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    sum: &pixel::AllocatedPixel<E>,
    num_elems: usize
) -> Result<pixel::AllocatedPixel<E>, SynthesisError>
where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    let num_value = pixel::AllocatedPixel::alloc(cs.namespace(|| "sum"), || {
		let mut value = sum.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?;
        Ok(value)
    })?;
    let res = meanEnforce(cs, || format!("sum"), &sum, &num_value, num_elems);

	Ok(num_value)
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
// Allocates a new variable as difference of two variables
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

/// Adds a constraint to CS, enforcing a difference square relationship between the allocated numbers a, b, and difference.
/// (a - b)^2 = difference^2
pub fn diffsqEnforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &pixel::AllocatedPixel<E>,
    b: &pixel::AllocatedPixel<E>,
    diffsq: &pixel::AllocatedPixel<E>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    //  a-b * a-b = diffsq

    cs.enforce(
        annotation,
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc + diffsq.get_variable(),
    );
}


// From storage-proofs/src/circuit/sloths.rs
// Allocates a new variable as difference of two variables
fn diffsq<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    a: &pixel::AllocatedPixel<E>,
    b: &pixel::AllocatedPixel<E>,
) -> Result<pixel::AllocatedPixel<E>, SynthesisError> {
    let res = pixel::AllocatedPixel::alloc(cs.namespace(|| "diffsq"), || {
        let mut tmp = a
            .get_value()
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        tmp.sub_assign(
            &b.get_value()
                .ok_or_else(|| SynthesisError::AssignmentMissing)?,
        );
        tmp.square();
		Ok(tmp)
    })?;

    // a - b = res
    difference(&mut cs, || "diffsq constraint", &a, &b, &res);

    Ok(res)
}

/// Adds a constraint to CS, enforcing a difference square relationship between the allocated numbers a, b, and difference.
/// (a - b)^2 = difference^2
pub fn diffmulEnforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &pixel::AllocatedPixel<E>,
	mean_a: &pixel::AllocatedPixel<E>,
    b: &pixel::AllocatedPixel<E>,
	mean_b: &pixel::AllocatedPixel<E>,
    res: &pixel::AllocatedPixel<E>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    //  a-mean_a * b-mean_b = res

    cs.enforce(
        annotation,
        |lc| lc + a.get_variable() - mean_a.get_variable(),
        |lc| lc + b.get_variable() - mean_b.get_variable(),
        |lc| lc + res.get_variable(),
    );
}
// From storage-proofs/src/circuit/sloths.rs
// Allocates a new variable as difference of two variables
fn diffmul<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    a: &pixel::AllocatedPixel<E>,
    mean_a: &pixel::AllocatedPixel<E>,
    b: &pixel::AllocatedPixel<E>,
    mean_b: &pixel::AllocatedPixel<E>,
) -> Result<pixel::AllocatedPixel<E>, SynthesisError> {


	let res = pixel::AllocatedPixel::alloc(cs.namespace(|| "diffmul"), || {
        let mut tmpa = a
            .get_value()
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        tmpa.sub_assign(
            &mean_a.get_value()
                .ok_or_else(|| SynthesisError::AssignmentMissing)?,
        );
       let mut tmpb = b
            .get_value()
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        tmpb.sub_assign(
            &mean_b.get_value()
                .ok_or_else(|| SynthesisError::AssignmentMissing)?,
        );
		let mut tmp = tmpa;
		tmp.mul_assign(&tmpb);
		Ok(tmp)
    })?;
    // ()a - mean_a) * ()b - bmean) = res
    diffmulEnforce(&mut cs, || "diffsq constraint", &a, &mean_a, &b, &mean_b, &res);

    Ok(res)
}
pub fn variance<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &Vec<pixel::AllocatedPixel<E>>,
	b: &Vec<pixel::AllocatedPixel<E>>,
	mean_a: &pixel::AllocatedPixel<E>,
	mean_b: &pixel::AllocatedPixel<E>
) -> Result<pixel::AllocatedPixel<E>, SynthesisError>
where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
	let mbSize = a.len();
	let mut varDiffSqMeanSrc : pixel::AllocatedPixel<E>;
	let mut vecADiffMul: Vec<_> = Vec::new();
	// sum diffsq src
    for i in 0..mbSize {
        let mut cs = cs.namespace(|| format!("diffsq {}", i));
        let value_num = diffmul(cs, &a[i], &mean_b, &b[i], &mean_b)?;
		vecADiffMul.push(value_num);
	}	

    let num_value = pixel::AllocatedPixel::alloc(cs.namespace(|| "sum var"), || {
	    let mut value = E::Fr::zero(); 
		for i in 0..mbSize {
			let pix = vecADiffMul[i].get_value();
			value.add_assign(&pix.unwrap());
		}    
		Ok(value)
    })?;

    let res = sumVec(cs, || format!("sum src"), &vecADiffMul).unwrap();

	Ok(num_value)
}



pub fn ssim_circuit_proof_verify(_src_pixel: Vec<u32>, _dst_pixel: Vec<u32>){
    use paired::bls12_381::{Bls12, Fr};
    use rand::thread_rng;
    use bellperson::groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof,
    };
    
    let rng = &mut thread_rng();
     // Create an instance of circuit

	let tmp_src_pixels: Vec<Option<Fr>> = _src_pixel.iter().map(|x| Some((Fr::from_repr(FrRepr::from(*x as u64))).unwrap())).collect();
	let tmp_dst_pixels: Vec<Option<Fr>> = _dst_pixel.iter().map(|x| Some((Fr::from_repr(FrRepr::from(*x as u64))).unwrap())).collect();

    let c = Ssim::<Bls12> {
		srcPixels: tmp_src_pixels.clone(),
		dstPixels: tmp_dst_pixels.clone()
    };

    // Create parameters for our circuit
    let params = {
        let c = Ssim::<Bls12> {
            srcPixels: tmp_src_pixels.clone(),
			dstPixels: tmp_dst_pixels.clone()
        };

        generate_random_parameters(c, rng).unwrap()
    };
    
    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");
    

    
    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(c, &params, rng).unwrap();
    let expected_inputs: Vec<Fr> = tmp_src_pixels.into_iter().map(|n| n.unwrap()).collect();  
    assert!(verify_proof(
        &pvk,
        &proof,
        &expected_inputs[..]
    ).unwrap());
}

#[cfg(test)]
mod test {
	use super::sumVec;
    use super::pixel::*;
	use super::ssim_circuit_proof_verify;
	use fil_sapling_crypto::circuit::boolean::{self, AllocatedBit, Boolean};
    use bellperson::{ConstraintSystem, SynthesisError};
    use storage_proofs::circuit::test::*;
    use ff::{BitIterator, Field, PrimeField};
    use paired::bls12_381::{Bls12, Fr};
    use rand::{Rand, Rng, SeedableRng, XorShiftRng};

	#[test]
	fn test_sumvec() {
		let mut cs = TestConstraintSystem::<Bls12>::new();
		// Prepare 3x3 test vector

		let mut var_pix3x3:  Vec<AllocatedPixel<Bls12>> = Vec::new();
		for i in 0..9 {
			let mut cs = cs.namespace(|| format!("src {}", i));
			let value = Some(Fr::from_str("3").unwrap());
			let value_num = AllocatedPixel::alloc(cs.namespace(|| format!("val {}", i)), || {
				value.ok_or_else(|| SynthesisError::AssignmentMissing)
	        });
			var_pix3x3.push(value_num.unwrap());
		}

		let sum = sumVec(&mut cs, || "sum vec", &var_pix3x3);
		//print!("Pixel variable={:?}", sum.unwrap().get_variable());
		assert!(sum.unwrap().get_value().unwrap() ==Fr::from_str("27").unwrap());
	}
	
/*	#[test]
	fn test_ssim_circuit_proof_verify() {		
		let _src_pixel: Vec<u32> = (0..256).map(|x| x).collect();
		let _dst_pixel: Vec<u32> = (0..256).map(|x| x).collect();
		ssim_circuit_proof_verify(_src_pixel, _dst_pixel);
	}*/
}