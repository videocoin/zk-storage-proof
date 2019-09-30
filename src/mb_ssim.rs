#![allow(unused_imports)]
#![allow(unused_variables)]
extern crate bellperson;
extern crate paired;
extern crate pbr;
extern crate rand;
use bellperson::{Circuit, ConstraintSystem, SynthesisError};
use paired::bls12_381::{Bls12, Fr, FrRepr};
use paired::Engine;

use super::pixel::*;
use ff::{BitIterator, Field, PrimeField, PrimeFieldRepr};
use fil_sapling_crypto::circuit::{boolean, multipack, num, pedersen_hash};

use rand::{Rng, SeedableRng, XorShiftRng};
use std::sync::{Arc, RwLock};
use storage_proofs::fr32::fr_into_bytes;

// We're going to use the Groth16 proving system.
use self::bellperson::groth16::{
	create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof,
};

#[derive(Clone)]
pub struct Ssim<E: Engine> {
	pub srcPixels: Vec<Option<E::Fr>>,
	pub dstPixels: Vec<Option<E::Fr>>,
}

impl<E: Engine> Circuit<E> for Ssim<E> {

	fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
/*		let mb_size = self.srcPixels.len();
		let mut varvec_src: Vec<_> = Vec::new();

		//let mut varvecDiffSqDst: Vec<_> = Vec::new();
		// Source pixel data
		let sum_src_64: u64 = 0;
		let sum_dst_64: u64 = 0;
		let var_variance_sum_src_u64 = 0;
		let var_variance_sum_dst_u64 = 0;
		let var_covariance_sum_u64 = 0;
		for i in 0..mb_size {
			let mut cs = cs.namespace(|| format!("src {}", i));
			let value = self.srcPixels[i];
			let value_num = pixel::AllocatedPixel::alloc(cs.namespace(|| "value"), || {
				value.ok_or_else(|| SynthesisError::AssignmentMissing)
			})?;
			value_num.inputize(cs.namespace(|| "value num"))?;
			varvec_src.push(value_num);
		}

		let mut var_vec_dst: Vec<_> = Vec::new();
		// Destination pixel data. Auxiliary input

		for i in 0..mb_size {
			let mut cs = cs.namespace(|| format!("dst {}", i));
			let value = self.dstPixels[i];
			let value_num = pixel::AllocatedPixel::alloc(cs.namespace(|| "value"), || {
				value.ok_or_else(|| SynthesisError::AssignmentMissing)
			})?;
			//value_num.inputize(cs.namespace(|| "value num"))?;
			var_vec_dst.push(value_num);
		}
		// div_constraint source
		let var_sum_src = sum_vec(cs, || ("sum src"), &varvec_src).unwrap();
		let var_mean_src = div_constraint(cs, || ("div_constraint src"), &var_sum_src, sum_src_64, mb_size).unwrap();

		let var_sum_dst = sum_vec(cs, || ("sum dst"), &var_vec_dst).unwrap();
		let var_mean_dst = div_constraint(cs, || ("div_constraint dst"), &var_sum_dst, sum_dst_64, mb_size).unwrap();

		let var_variance_sum_src = variance(
			cs,
			|| ("var sum src"),
			&varvec_src,
			&varvec_src,
			&var_mean_src,
			&var_mean_src,
		)
		.unwrap();
		let var_variance_sum_dst = variance(
			cs,
			|| ("var sum dst"),
			&var_vec_dst,
			&var_vec_dst,
			&var_mean_dst,
			&var_mean_dst,
		)
		.unwrap();
		let var_covariance_sum = variance(
			cs,
			|| ("covar sum"),
			&varvec_src,
			&var_vec_dst,
			&var_mean_src,
			&var_mean_dst,
		)
		.unwrap();
		let var_variance_src = div_constraint(cs, || ("var src"), &var_variance_sum_src, var_variance_sum_src_u64, mb_size).unwrap();
		let var_variance_dst = div_constraint(cs, || ("var dst"), &var_variance_sum_dst, var_variance_sum_dst_u64, mb_size).unwrap();
		let var_covariance = div_constraint(cs, || ("covar"), &var_covariance_sum, var_covariance_sum_u64, mb_size).unwrap();
*/
		Ok(())
	}
	
}

pub fn sum_vec<E: Engine,  CS: ConstraintSystem<E>>(
	mut cs: CS,
	a: &Vec<AllocatedPixel<E>>,
) -> Result<AllocatedPixel<E>, SynthesisError>
{
	let num_value = AllocatedPixel::alloc(cs.namespace(|| "sum"), || {
		let mb_size = a.len();
		let mut value = E::Fr::zero();
		for i in 0..mb_size {
			let pix = a[i].get_value();
			value.add_assign(&pix.unwrap());
		}
		Ok(value)
	})?;
	sum_vec_enforce(cs.namespace(|| "sum enforce"), || "sum enforce", &a, &num_value);

	Ok(num_value)
}

pub fn sum_vec_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	mut cs:  CS,
	annotation: A,
	a: &Vec<AllocatedPixel<E>>,
	sum: &AllocatedPixel<E>,
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

/// Adds a constraint to CS, enforcing a divide relation as multiplicaion.
/// quotient * denom = numerator - reminder
pub fn div_constraint_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	mut cs: CS,
	annotation: A,
	numerator: &AllocatedPixel<E>,
	denom: &AllocatedPixel<E>,
	quotient: &AllocatedPixel<E>,
	reminder: &AllocatedPixel<E>,
) where
	A: FnOnce() -> AR,
	AR: Into<String>,
{
	//  div_constraint * num_elems = sum

	cs.enforce(
		annotation,
		|lc| { lc + quotient.variable },	
		|lc| { lc + denom.variable },
		|lc| { lc + numerator.variable -  reminder.variable},
	);
}


/// Implements div (i.e. (numerator - reminder) / denom = quotient ) as mul (div_constraint * n = sum)
pub fn div_constraint<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	numerator: &AllocatedPixel<E>,
	numerator_u64: u64,
	denom_u64: u64,
) -> Result<AllocatedPixel<E>, SynthesisError>
{
	let num_samples = AllocatedPixel::alloc(cs.namespace(|| "div"), || {
		let value: E::Fr = (E::Fr::from_repr((denom_u64 as u64).into())).unwrap();
		Ok(value)
	})?;
	
	let quotient = AllocatedPixel::alloc(cs.namespace(|| "quotient"), || {
		let mean_val: u64 = numerator_u64 / denom_u64 as u64;
		let value: E::Fr = (E::Fr::from_repr(mean_val.into())).unwrap();
		Ok(value)
	})?;
	

	let reminder = AllocatedPixel::alloc(cs.namespace(|| "rem"), || {
		let reminder: u64 = numerator_u64 % denom_u64 as u64;//sum.get_value();
		let value: E::Fr = (E::Fr::from_repr(reminder.into())).unwrap();
		Ok(value)
	})?;
	
	div_constraint_enforce(cs, || "div_constraint enforce", &numerator, &num_samples, &quotient, &reminder);

	Ok(quotient)
}

pub fn ssim_lum<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	src_mean: &AllocatedPixel<E>,
	dst_mean: &AllocatedPixel<E>,
	c1_u64: u64,
	l_numerator_u64: u64,
	l_denominator_u64: u64,
) -> Result<AllocatedPixel<E>, SynthesisError>
{
	let c1 = AllocatedPixel::alloc(cs.namespace(|| "c1"), || {
		let value: E::Fr = (E::Fr::from_repr((c1_u64 as u64).into())).unwrap();
		Ok(value)
	})?;
	
	let uxuy = AllocatedPixel::alloc(cs.namespace(|| "uxuy"), || {
		let mut value: E::Fr = src_mean.get_value().unwrap();
		let mut value2: E::Fr = dst_mean.get_value().unwrap();
		value.mul_assign(&value2);		
		Ok(value)
	})?;
	cs.enforce(	|| "enforce uxuy", 
		|lc| { lc + src_mean.variable }, 	
		|lc| { lc + dst_mean.variable },
		|lc| { lc + uxuy.variable},
	);
		
	let ux_square = AllocatedPixel::alloc(cs.namespace(|| "ux_square"), || {
		let mut value: E::Fr = src_mean.get_value().unwrap();
		let mut value2: E::Fr = src_mean.get_value().unwrap();
		value.mul_assign(&value2);		
		Ok(value)
	})?;

	cs.enforce(	|| "enforce ux_square", 
		|lc| { lc + src_mean.variable }, 	
		|lc| { lc + src_mean.variable },
		|lc| { lc +  ux_square.variable},
	);
			
	let uy_square = AllocatedPixel::alloc(cs.namespace(|| "uy_square"), || {
		let mut value: E::Fr = dst_mean.get_value().unwrap();
		let mut value2: E::Fr = dst_mean.get_value().unwrap();
		value.mul_assign(&value2);
		print!("uy_square {:?}  {:?}  {:?}\n", dst_mean.get_value().unwrap(), value2, value);
		Ok(value)
	})?;	

	cs.enforce(	|| "enforce uy_square", 
		|lc| { lc + dst_mean.variable }, 	
		|lc| { lc + dst_mean.variable },
		|lc| { lc + uy_square.variable},
	);

	let lum_numerator = AllocatedPixel::alloc(cs.namespace(|| "lum numerator"), || {
		let value: E::Fr = (E::Fr::from_repr((l_numerator_u64 as u64).into())).unwrap();
		Ok(value)
	})?;	
	cs.enforce(	|| "enforce lum numerator", 
		|lc| { 
			let mut coeff = E::Fr::one();
			coeff.double();
			print!("coeff {:?}  \n",  coeff);	
			lc + (coeff, uxuy.variable) + c1.variable
		}, 	
		|lc| { lc + CS::one() },
		|lc| { lc + lum_numerator.variable},
	);	

	let lum_denom = AllocatedPixel::alloc(cs.namespace(|| "lum denom"), || {
		let value: E::Fr = (E::Fr::from_repr((l_denominator_u64 as u64).into())).unwrap();
		Ok(value)
	})?;	
	cs.enforce(	|| "enforce lum denom", 
		|lc| { lc + ux_square.variable + uy_square.variable + c1.variable}, 	
		|lc| { lc + CS::one() },
		|lc| { lc + lum_denom.variable},
	);	
	Ok(lum_numerator)
}

pub fn sqrt_constraint_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	mut cs: CS,
	annotation: A,
	sqr: &AllocatedPixel<E>,
	sqrt: &AllocatedPixel<E>,
	fract: &AllocatedPixel<E>,
) where
	A: FnOnce() -> AR,
	AR: Into<String>,
{
	//  div_constraint * num_elems = sum

	cs.enforce(
		annotation,
		|lc| { lc + sqrt.variable },	
		|lc| { lc + sqrt.variable },
		|lc| { lc + sqr.variable -  fract.variable},
	);
}
/// Implements div (i.e. (numerator - reminder) / denom = quotient ) as mul (div_constraint * n = sum)
pub fn sqrt_constraint<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	sqr: &AllocatedPixel<E>,
	sqrt_u64: u64,
	fract_u64: u64,
) -> Result<AllocatedPixel<E>, SynthesisError>
{
	let squrt = AllocatedPixel::alloc(cs.namespace(|| "div"), || {
		let value: E::Fr = (E::Fr::from_repr((sqrt_u64 as u64).into())).unwrap();
		Ok(value)
	})?;
	
	let fract = AllocatedPixel::alloc(cs.namespace(|| "quotient"), || {
		let value: E::Fr = (E::Fr::from_repr(fract_u64.into())).unwrap();
		Ok(value)
	})?;
	
	sqrt_constraint_enforce(cs, || "sqrt_constraint enforce", &sqr, &squrt, &fract);

	Ok(squrt)
}

/// Adds a constraint to CS, enforcing an equality relationship between the allocated numbers a and b.
///
/// a == b
#[allow(dead_code)]
pub fn equal<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	annotation: A,
	a: &AllocatedPixel<E>,
	b: &AllocatedPixel<E>,
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
/// 
#[allow(dead_code)]
pub fn difference<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	annotation: A,
	a: &AllocatedPixel<E>,
	b: &AllocatedPixel<E>,
	difference: &AllocatedPixel<E>,
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
#[allow(dead_code)]
fn sub<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	a: &AllocatedPixel<E>,
	b: &AllocatedPixel<E>,
) -> Result<AllocatedPixel<E>, SynthesisError> {
	let res = AllocatedPixel::alloc(cs.namespace(|| "sub num"), || {
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
#[allow(dead_code)]
pub fn diff_sq_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	annotation: A,
	a: &AllocatedPixel<E>,
	b: &AllocatedPixel<E>,
	diffsq: &AllocatedPixel<E>,
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
#[allow(dead_code)]
fn diffsq<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	a: &AllocatedPixel<E>,
	b: &AllocatedPixel<E>,
) -> Result<AllocatedPixel<E>, SynthesisError> {
	let res = AllocatedPixel::alloc(cs.namespace(|| "diffsq"), || {
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

	// (a - b) = res
	diff_sq_enforce(&mut cs, || "diffsq constraint", &a, &b, &res);

	Ok(res)
}

/// Adds a constraint to CS, enforcing a difference square relationship between the allocated numbers a, b, and difference.
/// (a - b)^2 = difference^2
#[allow(dead_code)]
pub fn diff_mul_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	annotation: A,
	a: &AllocatedPixel<E>,
	mean_a: &AllocatedPixel<E>,
	b: &AllocatedPixel<E>,
	mean_b: &AllocatedPixel<E>,
	res: &AllocatedPixel<E>,
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
#[allow(dead_code)]
fn diffmul<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	a: &AllocatedPixel<E>,
	mean_a: &AllocatedPixel<E>,
	b: &AllocatedPixel<E>,
	mean_b: &AllocatedPixel<E>,
) -> Result<AllocatedPixel<E>, SynthesisError> {
	let res = AllocatedPixel::alloc(cs.namespace(|| "diffmul"), || {
		let mut tmpa = a.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?;
		tmpa.sub_assign(&mean_a.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?,);
		let mut tmpb = b.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?;
		tmpb.sub_assign(&mean_b.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?,);
		let mut tmp = tmpa;
		tmp.mul_assign(&tmpb);
		Ok(tmp)
	})?;
	// ()a - mean_a) * ()b - mean_b) = res
	diff_mul_enforce(&mut cs,|| "diffsq constraint", &a, &mean_a, &b, &mean_b, &res,);

	Ok(res)
}

pub fn absdiff_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	annotation: A,
	a: &AllocatedPixel<E>,
	mean_a: &AllocatedPixel<E>,
	absdiff: &AllocatedPixel<E>,
) where
	A: FnOnce() -> AR,
	AR: Into<String>,
{

	cs.enforce(
		annotation,
		|lc| lc + a.get_variable() - mean_a.get_variable(),
		|lc| lc + CS::one(),
		|lc| lc + absdiff.get_variable(),
	);
}

fn absdiff<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	a: &AllocatedPixel<E>,
	mean_a: &AllocatedPixel<E>,
	sign: boolean::AllocatedBit,
) -> Result<AllocatedPixel<E>, SynthesisError> {
		
	let (c, d) = AllocatedPixel::conditionally_reverse(&mut cs, &a, &mean_a,  &boolean::Boolean::Is(sign)).unwrap();
	let res = AllocatedPixel::alloc(cs.namespace(|| "absdiff"), || {
		let mut tmp = c.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?;
		tmp.sub_assign(&d.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?,);
		Ok(tmp)
	})?;
	// ()a - mean_a) * ()b - mean_b) = res
	absdiff_enforce(&mut cs,|| "diffsq constraint", &c, &d, &res,);

	Ok(res)
}

pub fn variance<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	a: &Vec<AllocatedPixel<E>>,
	b: &Vec<AllocatedPixel<E>>,
	mean_a: &AllocatedPixel<E>,
	mean_b: &AllocatedPixel<E>,
	sign_a: &Vec<boolean::AllocatedBit>,
	sign_b: &Vec<boolean::AllocatedBit>,	
) -> Result<AllocatedPixel<E>, SynthesisError>
{
	let mb_size = a.len();
	let mut vecADiffMul: Vec<_> = Vec::new();
	// sum diffsq src
	for i in 0..mb_size {
		let mut cs = cs.namespace(|| format!("diffsq {}", i));
		
		//let value_num = diffmul(cs, &a[i], &mean_a, &b[i], &mean_b)?;
		let abs_diff_a = absdiff(cs.namespace(|| format!("diff a {}", i)), &a[i], &mean_a, sign_a[i].clone()).unwrap();
		let abs_diff_b = absdiff(cs.namespace(|| format!("diff b {}", i)), &b[i], &mean_b, sign_b[i].clone()).unwrap();
		let value_num = abs_diff_a.mul(cs.namespace(|| format!("diff ab {}", i)), &abs_diff_b).unwrap();
		vecADiffMul.push(value_num);
	}

	let num_value = AllocatedPixel::alloc(cs.namespace(|| "sum var"), || {
		let mut value = E::Fr::zero();
		for i in 0..mb_size {
			let pix = vecADiffMul[i].get_value();
			value.add_assign(&pix.unwrap());
		}
		Ok(value)
	})?;

	let res = sum_vec(cs.namespace( || format!("sum src")), &vecADiffMul).unwrap();

	Ok(num_value)
}

pub fn ssim_circuit_proof_verify(_src_pixel: Vec<u32>, _dst_pixel: Vec<u32>) {
	use bellperson::groth16::{
		create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof,
	};
	use paired::bls12_381::{Bls12, Fr};
	use rand::thread_rng;

	let rng = &mut thread_rng();
	// Create an instance of circuit

	let tmp_src_pixels: Vec<Option<Fr>> = _src_pixel
		.iter()
		.map(|x| Some((Fr::from_repr(FrRepr::from(*x as u64))).unwrap()))
		.collect();
	let tmp_dst_pixels: Vec<Option<Fr>> = _dst_pixel
		.iter()
		.map(|x| Some((Fr::from_repr(FrRepr::from(*x as u64))).unwrap()))
		.collect();

	let c = Ssim::<Bls12> {
		srcPixels: tmp_src_pixels.clone(),
		dstPixels: tmp_dst_pixels.clone(),
	};

	// Create parameters for our circuit
	let params = {
		let c = Ssim::<Bls12> {
			srcPixels: tmp_src_pixels.clone(),
			dstPixels: tmp_dst_pixels.clone(),
		};

		generate_random_parameters(c, rng).unwrap()
	};

	// Prepare the verification key (for proof verification)
	let pvk = prepare_verifying_key(&params.vk);

	println!("Creating proofs...");

	// Create a groth16 proof with our parameters.
	let proof = create_random_proof(c, &params, rng).unwrap();
	let expected_inputs: Vec<Fr> = tmp_src_pixels.into_iter().map(|n| n.unwrap()).collect();
	assert!(verify_proof(&pvk, &proof, &expected_inputs[..]).unwrap());
}

#[cfg(test)]
mod test {
	use super::*;
	use storage_proofs::circuit::test::*;

	fn gen_mb(mb_size: usize ) -> Vec<u32>  {	
		let mut rng = rand::thread_rng();
		let mb: Vec<u32> = (0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
		mb
	}

	fn get_mb_sum(mb: &Vec<u32> ) -> u32  {	
		let sum = mb.iter().map(|x| x).sum();
		sum
	}
	
	fn get_sqrt(x: u32 ) -> (u32, u32)  {	
		let sqrt_x = (x as f64).sqrt() as u32;
		(sqrt_x, x - sqrt_x * sqrt_x)
	}

	fn get_mb_covariance(mb_src: &Vec<u32>, mb_dst: &Vec<u32>, mean_src: u32, mean_dst: u32 ) -> u32 {
		let mut covar: u32 = 0;
		for it in mb_src.iter().zip(mb_dst.iter()) {
			let (src, dst) = it;
			let  mut a_diff: u32  = 0;
			let  mut b_diff: u32  = 0;
			if *src > mean_src {a_diff = *src  - mean_src} else {a_diff = mean_src - *src};
			if *dst > mean_dst {b_diff = *dst  - mean_dst} else {b_diff = mean_dst - *dst};
    		covar = covar + a_diff  * b_diff;
		}
		covar = covar  / mb_src.len() as u32;
		covar
	}

	fn gen_sample<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, mb: Vec<u32> ) -> Vec<AllocatedPixel<E>>  {
		// Prepare 3x3 test vector

		let mut var_pix3x3: Vec<AllocatedPixel<E>> = Vec::new();
		for i in 0..mb.len() {
			let value_num = AllocatedPixel::alloc(cs.namespace(|| format!("val {}", i)), || {
				let value = (E::Fr::from_repr((mb[i] as u64).into())).unwrap();
				Ok(value)
			});
			var_pix3x3.push(value_num.unwrap());
		}
		var_pix3x3
	}

	fn gen_sample_sign<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, mb: &Vec<u32>, mean: u32 ) -> Vec<boolean::AllocatedBit>  {
		let mut var_sign: Vec<boolean::AllocatedBit> = Vec::new();
		for i in 0..mb.len() {
			let cur_sign = boolean::AllocatedBit::alloc(
                cs.namespace(|| format!("sign {}", i)),
                if mb[i] > mean {Some(false)} else {Some(true)},
            );
			var_sign.push(cur_sign.unwrap());
		}
		var_sign
	}
	
/*
	#[test]
	fn test_lum_ssim() {
		let mut cs = TestConstraintSystem::<Bls12>::new();
		let src_mb = gen_mb(256);
		let dst_mb = gen_mb(256);		
		let var_src3x3 = gen_sample(cs.namespace(|| "src mb"), src_mb.clone());
		let var_dst3x3 = gen_sample(cs.namespace(|| "dst mb"), dst_mb.clone());
		let var_sum_src = sum_vec(cs.namespace(|| "src sum mb"), &var_src3x3).unwrap();
		let var_sum_dst = sum_vec(cs.namespace(|| "dst sum mb"), &var_dst3x3).unwrap();
		
		let num_samples = var_src3x3.len() as u32;

		let sum_src = get_mb_sum(&src_mb);
		let var_mean_src = div_constraint(cs.namespace(|| "src meant mb"), &var_sum_src, sum_src as u64, num_samples as u64).unwrap();

		let sum_dst = get_mb_sum(&dst_mb);
		let var_mean_dst = div_constraint(cs.namespace(|| "dst meant mb"), &var_sum_dst, sum_dst as u64, num_samples as u64).unwrap();
		let c1 = 0;
		let l_numerator = 2 * (sum_src / num_samples) * (sum_dst / num_samples) + c1; 
		let l_denom = ((sum_src / num_samples) * (sum_src / num_samples) + (sum_dst / num_samples) * (sum_dst / num_samples)) + c1;
		let l = ssim_lum(cs.namespace(|| "ssim lum"), &var_mean_src, &var_mean_dst, c1 as u64, l_numerator as u64, l_denom as u64);
		print!("inputs l_numerator={:?} l_denom={:?}\n", l_numerator, l_denom);
		print!("Num inputs: {:?}\n", cs.num_inputs());
		print!("Num constraints: {:?}\n", cs.num_constraints());
 
		print!("into_repr var_mean_src {:?}\n", var_mean_src.get_value().unwrap().into_repr());
		//println!("{}", cs.pretty_print());
		assert!(var_mean_src.get_value().unwrap() == (Fr::from_repr(((sum_src/num_samples) as u64).into())).unwrap());
		assert!(cs.is_satisfied());
	}
*/	
	#[test]
	fn test_struct_ssim() {
		let mut cs = TestConstraintSystem::<Bls12>::new();
		let src_mb = gen_mb(9);
		let dst_mb = gen_mb(9);		
		let var_src3x3 = gen_sample(cs.namespace(|| "src mb"), src_mb.clone());
		let var_dst3x3 = gen_sample(cs.namespace(|| "dst mb"), dst_mb.clone());
		let var_sum_src = sum_vec(cs.namespace(|| "src sum mb"), &var_src3x3).unwrap();
		let var_sum_dst = sum_vec(cs.namespace(|| "dst sum mb"), &var_dst3x3).unwrap();
		
		let witness_num_samples = var_src3x3.len() as u32;

		let witness_sum_src = get_mb_sum(&src_mb);
		let circ_mean_src = div_constraint(cs.namespace(|| "src meant mb"), &var_sum_src, witness_sum_src as u64, witness_num_samples as u64).unwrap();

		let witness_sum_dst = get_mb_sum(&dst_mb);
		let circ_mean_dst = div_constraint(cs.namespace(|| "dst meant mb"), &var_sum_dst, witness_sum_dst as u64, witness_num_samples as u64).unwrap();


		// Structure
		let circ_src_sign = gen_sample_sign(cs.namespace(|| "sign src"), &src_mb, witness_sum_src / witness_num_samples);
		let circ_dst_sign = gen_sample_sign(cs.namespace(|| "sign dst"), &src_mb, witness_sum_dst / witness_num_samples);
		
		let withness_variance_src = get_mb_covariance(&src_mb, &src_mb, witness_sum_src / witness_num_samples, witness_sum_src / witness_num_samples);
		let circ_variance_src = variance(cs.namespace(|| "variance src"), &var_src3x3, &var_src3x3, &circ_mean_src, &circ_mean_src,  &circ_src_sign, &circ_src_sign).unwrap();
		let (withness_variance_sqrt_src, withness_variance_reminder_src) = get_sqrt(withness_variance_src);
		//let circ_sigma_src = div_constraint(cs.namespace(|| "sigma src"), &circ_variance_src, withness_variance_src as u64, withness_variance_sqrt_src as u64).unwrap();

		
		let withness_variance_dst = get_mb_covariance(&dst_mb, &dst_mb, witness_sum_dst / witness_num_samples, witness_sum_dst / witness_num_samples);
		let circ_variance_dst = variance(cs.namespace(|| "variance dst"), &var_dst3x3, &var_dst3x3, &circ_mean_dst, &circ_mean_dst,  &circ_dst_sign, &circ_dst_sign).unwrap();

		let withness_covariance = get_mb_covariance(&src_mb, &dst_mb, witness_sum_src / witness_num_samples, witness_sum_dst/ witness_num_samples);
		
		let circ_covariance = variance(cs.namespace(|| "covariance"), &var_src3x3, &var_dst3x3, &circ_mean_src, &circ_mean_dst, &circ_src_sign, &circ_dst_sign).unwrap();
		let (withness_covariance_sqrt, withness_covariance_reminder) = get_sqrt(withness_covariance);
		let s_numerator = sqrt_constraint(cs.namespace(|| "sigma xy"), &circ_covariance, withness_covariance as u64, withness_covariance_sqrt as u64).unwrap();

		let c3 = 0;
		//let s_numerator = 2 * (sum_src / num_samples) * (sum_dst / num_samples) + c3; 
		//let s_denom = ((sum_src / num_samples) * (sum_src / num_samples) + (sum_dst / num_samples) * (sum_dst / num_samples)) + c1;
		//let s = ssim_struct(cs.namespace(|| "ssim lum"), &var_mean_src, &var_mean_dst, c1 as u64, l_numerator as u64, l_denom as u64);
		//print!("inputs l_numerator={:?} l_denom={:?}\n", l_numerator, l_denom);
		print!("Num inputs: {:?}\n", cs.num_inputs());
		print!("Num constraints: {:?}\n", cs.num_constraints());
		print!("withness_covariance={:?} sqrt={:?} rem={:?}",withness_covariance, withness_covariance_sqrt, withness_covariance_reminder);
		assert!(cs.is_satisfied());
	}	
}
