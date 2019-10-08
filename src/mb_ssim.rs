#![allow(unused_imports)]
#![allow(unused_variables)]
extern crate bellperson;
extern crate paired;
extern crate pbr;
extern crate rand;
use bellperson::{Circuit, ConstraintSystem, SynthesisError};
use paired::bls12_381::{Bls12, Fr, FrRepr};
use paired::Engine;
use std::marker::PhantomData;

use super::pixel::*;
use ff::{BitIterator, Field, PrimeField, PrimeFieldRepr};
use fil_sapling_crypto::circuit::{boolean, multipack, num, pedersen_hash};

use rand::{Rng, SeedableRng, XorShiftRng, thread_rng};
use std::sync::{Arc, RwLock};
use storage_proofs::fr32::fr_into_bytes;

// We're going to use the Groth16 proving system.
use self::bellperson::groth16::{
	create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof, Parameters, PreparedVerifyingKey
};

#[derive(Clone)]
pub struct Ssim<E: Engine> {
	src_mb: Vec<u32>, 
	dst_mb: Vec<u32>,	
	pub witns: Witness,
	phantom: PhantomData<E>,	
}

impl<E: Engine> Circuit<E> for Ssim<E> {

	fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
		let (circ_ssim_numerator, circ_ssim_denom) = ssim_circuit(cs.namespace(|| "ssim"), self).unwrap();
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
	let squrt = AllocatedPixel::alloc(cs.namespace(|| "squrt"), || {
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

//=======

pub fn mul_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	annotation: A,
	a: &AllocatedPixel<E>,
	b: &AllocatedPixel<E>,
	res: &AllocatedPixel<E>,
) where
	A: FnOnce() -> AR,
	AR: Into<String>,
{
	//  a-mean_a * b-mean_b = res

	cs.enforce(
		annotation,
		|lc| lc + a.get_variable(),
		|lc| lc + b.get_variable(),
		|lc| lc + res.get_variable(),
	);
}


fn mul<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	a: &AllocatedPixel<E>,
	b: &AllocatedPixel<E>,
) -> Result<AllocatedPixel<E>, SynthesisError> {
	let res = AllocatedPixel::alloc(cs.namespace(|| "mul"), || {
		let mut tmpa = a.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?;
		let mut tmpb = b.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?;
		tmpa.mul_assign(&tmpb);
		Ok(tmpa)
	})?;
	// ()a - mean_a) * ()b - mean_b) = res
	mul_enforce(&mut cs,|| "diffsq constraint", &a, &b, &res,);

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
	//print!("sign={:?}\n", boolean::Boolean::Is(sign.clone()).get_value());	
	let (c, d) = AllocatedPixel::conditionally_reverse(&mut cs, &a, &mean_a,  &boolean::Boolean::Is(sign)).unwrap();
	let res = AllocatedPixel::alloc(cs.namespace(|| "absdiff"), || {
		let mut tmp = c.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?;
		tmp.sub_assign(&d.get_value().ok_or_else(|| SynthesisError::AssignmentMissing)?,);
		//print!("absdiff c={:?} d={:?} a={:} mean={:}\n",  c.get_value().unwrap(), d.get_value().unwrap(), a.get_value().unwrap(), mean_a.get_value().unwrap());
		Ok(tmp)
	})?;
	// ()a - mean_a) * ()b - mean_b) = res
	absdiff_enforce(&mut cs,|| "diffsq constraint", &c, &d, &res,);

	Ok(res)
}

pub fn absdiff_vec<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	a: &Vec<AllocatedPixel<E>>,
	mean_a: &AllocatedPixel<E>,
	sign_a: &Vec<boolean::AllocatedBit>,
) -> Vec<AllocatedPixel<E>>
{
	let mb_size = a.len();
	let mut diff_vec: Vec<_> = Vec::new();
	for i in 0..mb_size {
		let abs_diff = absdiff(cs.namespace(|| format!("diff a {}", i)), &a[i], &mean_a, sign_a[i].clone()).unwrap();
		diff_vec.push(abs_diff);
	}
	diff_vec
}

pub fn variance<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	diff_vec_a: &Vec<AllocatedPixel<E>>,
	diff_vec_b: &Vec<AllocatedPixel<E>>,	
) -> Result<AllocatedPixel<E>, SynthesisError>
{
	let mb_size = diff_vec_a.len();
	let mut diff_prod_vec: Vec<_> = Vec::new();
	//let mut diff_vec_a = absdiff_vec(cs.namespace(|| "absdiff a"), a, mean_a, sign_a);
	//let mut diff_vec_b = absdiff_vec(cs.namespace(|| "abs diff b"), b, mean_b, sign_b);
	for i in 0..mb_size {
		let mut cs = cs.namespace(|| format!("diffsq {}", i));
		
		//let value_num = diffmul(cs, &a[i], &mean_a, &b[i], &mean_b)?;
		let abs_diff_a = &diff_vec_a[i];//absdiff(cs.namespace(|| format!("diff a {}", i)), &a[i], &mean_a, sign_a[i].clone()).unwrap();
		let abs_diff_b = &diff_vec_b[i];//absdiff(cs.namespace(|| format!("diff b {}", i)), &b[i], &mean_b, sign_b[i].clone()).unwrap();
		//let value_num = abs_diff_a.mul(cs.namespace(|| format!("diff ab {}", i)), &abs_diff_b).unwrap();
		let value_num = mul(cs.namespace(|| format!("diff ab {}", i)), &abs_diff_a, &abs_diff_b).unwrap();
		//print!("variance elem pass1 = {:?}\n", value_num.get_value().unwrap());
		diff_prod_vec.push(value_num);
	}

	let num_value = AllocatedPixel::alloc(cs.namespace(|| "sum var"), || {
		let mut value = E::Fr::zero();
		for i in 0..mb_size {
			let pix = diff_prod_vec[i].get_value();
			print!("variance elem pass 2= {:?}\n", pix.unwrap());
			value.add_assign(&pix.unwrap());
		}
		Ok(value)
	})?;

	Ok(num_value)
}

pub fn covairance_constraint<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS, 
	circ_abs_diff_vec_x: &Vec<AllocatedPixel<E>>, 
	cirs_abs_diff_vec_y: &Vec<AllocatedPixel<E>>,
	witness_sigma_sq_sum: u32,
	withness_sigma: u32,
	withness_sigma_frac: u32,
	) -> (AllocatedPixel<E>, AllocatedPixel<E>, AllocatedPixel<E>) {
	let witness_num_samples = circ_abs_diff_vec_x.len();
	let circ_sigma_sq_sum = variance(cs.namespace(|| "covariance sum"), &circ_abs_diff_vec_x, &cirs_abs_diff_vec_y).unwrap();
	let circ_sigma_sq = div_constraint(cs.namespace(|| "sigma sq sum"), &circ_sigma_sq_sum, witness_sigma_sq_sum as u64, witness_num_samples as u64).unwrap();
	let circ_sigma = sqrt_constraint(cs.namespace(|| "sigma"), &circ_sigma_sq, withness_sigma as u64, withness_sigma_frac as u64).unwrap();
	(circ_sigma_sq_sum, circ_sigma_sq, circ_sigma)
}


///
/// Constriant for luma or contrast.
/// Incase of contrast src_mean is interepreted as sigma_x, dst_mean as sigma_y and c1 as c2
/// 
pub fn ssim_lum_or_contrast<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	src_mean: &AllocatedPixel<E>,
	dst_mean: &AllocatedPixel<E>,
	c1_u64: u64,
	l_numerator_u64: u64,
	l_denominator_u64: u64,
) -> Result<(AllocatedPixel<E>,AllocatedPixel<E>,AllocatedPixel<E>), SynthesisError>
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
	Ok((lum_numerator, lum_denom, c1))
}


pub fn ssim_struct_constraint<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	sigma_xy: &AllocatedPixel<E>,
	sigma_x: &AllocatedPixel<E>,
	sigma_y: &AllocatedPixel<E>,
	witness_c3: u64,
	witness_s_numerator: u64,
	witness_s_denominator: u64,
) -> Result<(AllocatedPixel<E>, AllocatedPixel<E>), SynthesisError>//-> (AllocatedPixel<E>, AllocatedPixel<E>)
{
	let circ_c3 = AllocatedPixel::alloc(cs.namespace(|| "c3"), || {
		let value: E::Fr = (E::Fr::from_repr((witness_c3 as u64).into())).unwrap();
		Ok(value)
	})?;

	let s_numerator = AllocatedPixel::alloc(cs.namespace(|| "lum numerator"), || {
		let value: E::Fr = (E::Fr::from_repr((witness_s_numerator as u64).into())).unwrap();
		Ok(value)
	})?;	
	cs.enforce(	|| "enforce lum numerator", 
		|lc| { 
			lc +  sigma_xy.variable + circ_c3.variable
		}, 	
		|lc| { lc + CS::one() },
		|lc| { lc + s_numerator.variable},
	);	

	let s_denom = AllocatedPixel::alloc(cs.namespace(|| "s denom"), || {
		let value: E::Fr = (E::Fr::from_repr((witness_s_denominator as u64).into())).unwrap();
		Ok(value)
	})?;	
	cs.enforce(	|| "enforce lum denom", 
		|lc| { lc + sigma_x.variable}, 	
		|lc| { lc + sigma_y.variable },
		|lc| { lc + s_denom.variable - circ_c3.variable},
	);	
	//(s_numerator, s_denom)
	Ok((s_numerator,s_denom))
}

pub fn ssim_constraint<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	ssim_l_numerator: &AllocatedPixel<E>,
	sigma_xy: &AllocatedPixel<E>,
	circ_c2: &AllocatedPixel<E>,	
	ssim_l_denom: &AllocatedPixel<E>,
	ssim_c_denom: &AllocatedPixel<E>,
	witness_s_numerator: u64,
	witness_s_denominator: u64,
) -> Result<(AllocatedPixel<E>, AllocatedPixel<E>), SynthesisError>//-> (AllocatedPixel<E>, AllocatedPixel<E>)
{

	let s_numerator = AllocatedPixel::alloc(cs.namespace(|| "lum numerator"), || {
		let value: E::Fr = (E::Fr::from_repr((witness_s_numerator as u64).into())).unwrap();
		Ok(value)
	})?;	
	cs.enforce(	|| "enforce lum numerator", 
		|lc| { lc +  ssim_l_numerator.variable }, 	
		|lc| { 
			let mut coeff = E::Fr::one();
			coeff.double();
			lc + (coeff,  sigma_xy.variable) + circ_c2.variable
		},
		|lc| { lc + s_numerator.variable},
	);	

	let s_denom = AllocatedPixel::alloc(cs.namespace(|| "s denom"), || {
		let value: E::Fr = (E::Fr::from_repr((witness_s_denominator as u64).into())).unwrap();
		Ok(value)
	})?;	
	cs.enforce(	|| "enforce lum denom", 
		|lc| { lc + ssim_l_denom.variable}, 	
		|lc| { lc + ssim_c_denom.variable },
		|lc| { lc + s_denom.variable},
	);	
	//(s_numerator, s_denom)
	Ok((s_numerator,s_denom))
}

pub fn ssim_circuit<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	c: Ssim::<E>,
) -> Result<(AllocatedPixel<E>, AllocatedPixel<E>), SynthesisError> {
	let mut witns = c.witns;
	let circ_mb_x = gen_sample(cs.namespace(|| "src mb"), c.src_mb.clone());
	let circ_mb_y = gen_sample(cs.namespace(|| "dst mb"), c.dst_mb.clone());
	let circ_mb_sum_x = sum_vec(cs.namespace(|| "src sum mb"), &circ_mb_x).unwrap();
	let circ_mb_sum_y = sum_vec(cs.namespace(|| "dst sum mb"), &circ_mb_y).unwrap();
	
	let circ_mean_src = div_constraint(cs.namespace(|| "src meant mb"), &circ_mb_sum_x, witns.sum_src as u64, witns.num_samples as u64).unwrap();
	let circ_mean_dst = div_constraint(cs.namespace(|| "dst meant mb"), &circ_mb_sum_y, witns.sum_dst as u64, witns.num_samples as u64).unwrap();
	
	
	let (circ_l_numerator, circ_l_denom, c1_crc) = ssim_lum_or_contrast(cs.namespace(|| "ssim lum"), &circ_mean_src, &circ_mean_dst, witns.c1 as u64, witns.l_numerator as u64, witns.l_denom as u64).unwrap();
	
	//
	// Structure
	//
	let circ_src_sign = gen_sample_sign(cs.namespace(|| "sign src"), &c.src_mb, witns.sum_src / witns.num_samples);
	let circ_dst_sign = gen_sample_sign(cs.namespace(|| "sign dst"), &c.dst_mb, witns.sum_dst / witns.num_samples);
	
	let mut circ_diff_vec_src = absdiff_vec(cs.namespace(|| "absdiff a"), &circ_mb_x, &circ_mean_src, &circ_src_sign);
	let mut circ_diff_vec_dst = absdiff_vec(cs.namespace(|| "abs diff b"),  &circ_mb_y, &circ_mean_dst, &circ_dst_sign);

	let (circ_sigma_x_sq_sum, circ_sigma_x_sq, circ_sigma_x) = covairance_constraint(cs.namespace(|| "sigma x const"), 
			&circ_diff_vec_src, &circ_diff_vec_src, witns.sigma_x_sq_sum, witns.sigma_x, witns.sigma_x_frac);

	let (circ_sigma_y_sq_sum, circ_sigma_y_sq, circ_sigma_y) = covairance_constraint(cs.namespace(|| "sigma y const"), 
			&circ_diff_vec_dst, &circ_diff_vec_dst, witns.sigma_y_sq_sum, witns.sigma_y, witns.sigma_y_frac);

	let (circ_sigma_xy_sq_sum, circ_sigma_xy_sq, circ_sigma_xy) = covairance_constraint(cs.namespace(|| "sigma xy const"), 
			&circ_diff_vec_src, &circ_diff_vec_dst, witns.sigma_xy_sq_sum, witns.sigma_xy, witns.sigma_xy_frac);
	
	let (circ_s_numerator, circ_s_denom) = ssim_struct_constraint(cs.namespace(|| "ssim struct"), &circ_sigma_xy, &circ_sigma_x, &circ_sigma_y, witns.c3 as u64, witns.s_numerator as u64, witns.s_denom as u64).unwrap();
	//
	// contrast
	//
	let (circ_c_numerator, circ_c_denom, c2_circ) = ssim_lum_or_contrast(cs.namespace(|| "ssim contrast"), &circ_sigma_x, &circ_sigma_y, witns.c2 as u64, witns.c_numerator as u64, witns.c_denom as u64).unwrap();
	//
	// ssim
	//
	let (circ_ssim_numerator, circ_ssim_denom) = ssim_constraint(cs.namespace(|| "ssim constraint"), &circ_l_numerator, &circ_sigma_xy, &c2_circ, &circ_l_denom, &circ_c_denom, witns.ssim_numerator as u64, witns.ssim_denom as u64).unwrap();
	Ok((circ_ssim_numerator, circ_ssim_denom))
}

/// Generate a unique cache path, based on the inputs.
fn get_cache_path(
    name: &str,
    version: usize,
) -> String {
    format!(
        "/tmp/videocoin-ssim-proofs-cache-{}-{}",
        name.to_ascii_lowercase(),
        version,
    )
}

pub fn ssim_circuit_proof_verify(
	_src_pixel: Vec<u32>, 
	_dst_pixel: Vec<u32>,
	_witns: Witness,) {
	use bellperson::groth16::{
		create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof,
	};
	use paired::bls12_381::{Bls12, Fr};
	use rand::thread_rng;

	let rng = &mut thread_rng();
	// Create an instance of circuit
	
	let c = Ssim::<Bls12> {
		src_mb: _src_pixel.clone(),
		dst_mb: _dst_pixel.clone(),		
		witns: _witns.clone(),
		phantom: Default::default(),
	};

	// Create parameters for our circuit
	let params = {
		let c = Ssim::<Bls12> {
			src_mb: _src_pixel.clone(),
			dst_mb: _dst_pixel.clone(),
			witns: _witns.clone(),
			phantom: Default::default(),
		};

		generate_random_parameters(c, rng).unwrap()
	};

	// Prepare the verification key (for proof verification)
	let pvk = prepare_verifying_key(&params.vk);

	println!("Creating proofs...");

	// Create a groth16 proof with our parameters.
	let proof = create_random_proof(c, &params, rng).unwrap();
	//let expected_inputs: Vec<Fr> = tmp_src_pixels.into_iter().map(|n| n.unwrap()).collect();
	//assert!(verify_proof(&pvk, &proof, &expected_inputs[..]).unwrap());
	let end = 0;
}





///
/// Utility functions
///

/// generate random input macroblock
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
	covar
}

fn get_witness(src_mb: &Vec<u32>, dst_mb: &Vec<u32>) -> (u32, u32, u32, u32) {
	
	let sum_src = get_mb_sum(src_mb);
	let sum_dst = get_mb_sum(dst_mb);
	let num_samples: u32 = src_mb.len() as u32;
	let sigma_sq_sum = get_mb_covariance(&src_mb, &dst_mb, sum_src / num_samples, sum_dst/ num_samples);
	let sigma_sq = sigma_sq_sum / num_samples;		
	let (sigma, sigma_frac) = get_sqrt(sigma_sq);
	(sigma_sq_sum, sigma_sq, sigma, sigma_frac)
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

/// Wrapper for SSIM API
pub struct SsimApp {
    mb_size: u32,
	src_pixel: Vec<u32>, 
    dst_pixel: Vec<u32>,
	witns: Witness,
}

impl Default for SsimApp {
    fn default() -> Self {
		let rng = &mut thread_rng();
		let mb_size = 256;
		let src_pixel: Vec<u32>  = (0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
		let dst_pixel: Vec<u32> =(0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
		let witns = gen_witness(&src_pixel.clone(), &dst_pixel.clone());
        SsimApp {
			mb_size,
            src_pixel,
            dst_pixel, 
			witns
        }
    }
}

/// A trait that makes it easy to implement SSIM API
pub trait SsimApi<'a, C: Circuit<Bls12>>: Default {
	/// The name of the application. Used for identifying caches.
    fn name() -> String;

    /// Generate groth parameters.
	/// arguments _src_pixel etc are random
    fn setup(
        &mut self,
    ) -> Parameters<Bls12>;

    #[allow(clippy::too_many_arguments)]
    fn create_proof(
        &mut self,
        groth_params: &Parameters<Bls12>,
		src_pixel: Vec<u32>, 
	    dst_pixel: Vec<u32>,
		witns: Witness,		
    ) -> Proof<Bls12>;

    /// Verify the given proof, return `None` if not implemented.
    fn verify_proof(
		&mut self, 
        pvk: &PreparedVerifyingKey<Bls12>,		
		proof: &Proof<Bls12>,
		public_inputs: Vec<u32>) -> Option<bool>;
}

impl<'a> SsimApi<'a, Ssim<Bls12>> for SsimApp {
    fn name() -> String {
        "Ssim".to_string()
    }

    fn setup(
        &mut self,
    ) -> Parameters<Bls12> {
		// Create parameters for our circuit
		let rng = &mut thread_rng();
		let params = {
			let c = Ssim::<Bls12> {
				src_mb: self.src_pixel.clone(),
				dst_mb: self.dst_pixel.clone(),
				witns:  self.witns.clone(),
				phantom: Default::default(),
			};
	
			generate_random_parameters(c, rng).unwrap()
		};
		params
    }

    fn create_proof(
        &mut self,
		groth_params: &Parameters<Bls12>,
		src_pixel: Vec<u32>, 
	    dst_pixel: Vec<u32>,
		witns: Witness,		
    ) -> Proof<Bls12> {
		let rng = &mut thread_rng();
		let c = Ssim::<Bls12> {
			src_mb: src_pixel.clone(),
			dst_mb: dst_pixel.clone(),
			witns:  witns.clone(),
			phantom: Default::default(),
		};

        create_random_proof(c, groth_params, rng).expect("failed to create proof")

    }

    fn verify_proof(
        &mut self,
        pvk: &PreparedVerifyingKey<Bls12>,
        proof: &Proof<Bls12>,
		public_inputs: Vec<u32>,
    ) -> Option<bool> {
        let expected_inputs: Vec<Fr> = public_inputs.iter().map(|x| (Fr::from_repr((*x as u64).into())).unwrap()).collect();
        // -- verify proof with public inputs
        Some(verify_proof(pvk, proof, &expected_inputs).expect("failed to verify proof"))
    }
}

#[derive(Clone)]
#[derive(Default)]
pub struct Witness {
	num_samples: u32,
	sum_src: u32,
	sum_dst: u32,
	l_numerator: u32,
	l_denom: u32,
	c1: u32,
	
	sigma_x_sq_sum: u32, 
	sigma_x_sq: u32, 
	sigma_x: u32, 
	sigma_x_frac: u32,
	
	sigma_y_sq_sum: u32, 
	sigma_y_sq: u32, 
	sigma_y: u32, 
	sigma_y_frac: u32,
	
	sigma_xy_sq_sum: u32, 
	sigma_xy_sq: u32, 
	sigma_xy: u32, 
	sigma_xy_frac: u32,

	s_numerator: u32,
	s_denom: u32,
	c3: u32,
	c_numerator: u32,
	c_denom: u32,
	c2: u32,
	
	ssim_numerator: u32,
	ssim_denom: u32
}	


pub fn gen_witness(src_mb: &Vec<u32>, dst_mb: &Vec<u32>) -> Witness {
	
		let num_samples = src_mb.len() as u32;
		let sum_src = get_mb_sum(&src_mb);
		let sum_dst = get_mb_sum(&dst_mb);

		//
		// Lumen
		//
		let c1 = 0;
		let l_numerator = 2 * (sum_src / num_samples) * (sum_dst / num_samples) + c1; 
		let l_denom = ((sum_src / num_samples) * (sum_src / num_samples) + (sum_dst / num_samples) * (sum_dst / num_samples)) + c1;
		let (sigma_x_sq_sum, sigma_x_sq, sigma_x, sigma_x_frac)= get_witness(&src_mb, &src_mb);		
		let (sigma_y_sq_sum, sigma_y_sq, sigma_y, sigma_y_frac)= get_witness(&dst_mb, &dst_mb);
		let (sigma_xy_sq_sum, sigma_xy_sq, sigma_xy, sigma_xy_frac)= get_witness(&src_mb, &dst_mb);
		let c3 = 0;
		let s_numerator = sigma_xy + c3; 
		let s_denom = sigma_x * sigma_y  + c3;
		let c2 = 0;
		let c_numerator = 2 * sigma_x * sigma_y + c2; 
		let c_denom = (sigma_x * sigma_x) + (sigma_y * sigma_y) + c3;
		let ssim_numerator = l_numerator * 2 * sigma_xy + c2;
		let ssim_denom = l_denom * c_denom;
		
		let mut witns = Witness {
			num_samples,
			sum_src,
			sum_dst,
			l_numerator,
			l_denom,
			c1,
			
			sigma_x_sq_sum, 
			sigma_x_sq, 
			sigma_x, 
			sigma_x_frac,
			
			sigma_y_sq_sum, 
			sigma_y_sq, 
			sigma_y, 
			sigma_y_frac,
			
			sigma_xy_sq_sum, 
			sigma_xy_sq, 
			sigma_xy, 
			sigma_xy_frac,
	
			
			s_numerator,
			s_denom,
			c3,
			
			c_numerator,
			c_denom,
			c2,
			
			ssim_numerator,
			ssim_denom,
		};
		
		witns
}
	
#[cfg(test)]
mod test {
	use super::*;
	use storage_proofs::circuit::test::*;


	#[test]
	fn test_struct_ssim() {
		let mut cs = TestConstraintSystem::<Bls12>::new();
		let src_mb = gen_mb(256);
		let dst_mb = gen_mb(256);		
		
		let witns = gen_witness(&src_mb, &dst_mb);
		let tmp_src_pixels: Vec<Option<Fr>> = src_mb
			.iter()
			.map(|x| Some((Fr::from_repr(FrRepr::from(*x as u64))).unwrap()))
			.collect();
		let tmp_dst_pixels: Vec<Option<Fr>> = dst_mb
			.iter()
			.map(|x| Some((Fr::from_repr(FrRepr::from(*x as u64))).unwrap()))
			.collect();
	
		let c = Ssim::<Bls12> {
			src_mb: src_mb.clone(),
			dst_mb: dst_mb.clone(),			
			witns: witns.clone(),
			phantom: Default::default(),
		};
			
		let (circ_ssim_numerator, circ_ssim_denom) = ssim_circuit(cs.namespace(|| "ssim"), c).unwrap();
		//print!("inputs l_numerator={:?} l_denom={:?}\n", l_numerator, l_denom);
		//print!("Num inputs: {:?}\n", cs.num_inputs());
		print!("Num constraints: {:?}\n", cs.num_constraints());
		print!("witns.covariance={:?} sqrt={:?} rem={:?}",witns.sigma_xy_sq, witns.sigma_xy, witns.sigma_xy_frac);
		//print!("circ_sigma_sq={:?} circ_sigma={:?} ",circ_sigma_xy_sq.value, circ_sigma_xy.value);

		assert!(cs.is_satisfied());
	}	
}
