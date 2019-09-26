#![allow(unused_imports)]
#![allow(unused_variables)]
extern crate bellperson;
extern crate paired;
extern crate pbr;
extern crate rand;
use bellperson::{Circuit, ConstraintSystem, SynthesisError};
use paired::bls12_381::{Bls12, Fr, FrRepr};
use paired::Engine;

use super::pixel;
use ff::Field;
use ff::PrimeField;
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
		let mb_size = self.srcPixels.len();
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
		// mean source
		let var_sum_src = sum_vec(cs, || ("sum src"), &varvec_src).unwrap();
		let var_mean_src = mean(cs, || ("mean src"), &var_sum_src, sum_src_64, mb_size).unwrap();

		let var_sum_dst = sum_vec(cs, || ("sum dst"), &var_vec_dst).unwrap();
		let var_mean_dst = mean(cs, || ("mean dst"), &var_sum_dst, sum_dst_64, mb_size).unwrap();

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
		let var_variance_src = mean(cs, || ("var src"), &var_variance_sum_src, var_variance_sum_src_u64, mb_size).unwrap();
		let var_variance_dst = mean(cs, || ("var dst"), &var_variance_sum_dst, var_variance_sum_dst_u64, mb_size).unwrap();
		let var_covariance = mean(cs, || ("covar"), &var_covariance_sum, var_covariance_sum_u64, mb_size).unwrap();

		Ok(())
	}
}

pub fn sum_vec<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	annotation: A,
	a: &Vec<pixel::AllocatedPixel<E>>,
) -> Result<pixel::AllocatedPixel<E>, SynthesisError>
where
	A: FnOnce() -> AR,
	AR: Into<String>,
{
	let num_value = pixel::AllocatedPixel::alloc(cs.namespace(|| "sum"), || {
		let mb_size = a.len();
		let mut value = E::Fr::zero();
		for i in 0..mb_size {
			let pix = a[i].get_value();
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

/// Adds a constraint to CS, enforcing a mean relationship between sum and num_elems.
/// (a - b)^2 = difference^2
pub fn mean_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	annotation: A,
	sum: &pixel::AllocatedPixel<E>,
	num_samples: &pixel::AllocatedPixel<E>,
	mean_int: &pixel::AllocatedPixel<E>,
	mean_rem: &pixel::AllocatedPixel<E>,
) where
	A: FnOnce() -> AR,
	AR: Into<String>,
{
	//  mean * num_elems = sum

	cs.enforce(
		annotation,
		|lc| { lc + mean_int.variable },	
		|lc| { lc + num_samples.variable },
		|lc| { lc + sum.variable -  mean_rem.variable},
	);
}


/// Implements div (i.e. mean = sum / n) as mul (mean * n = sum)
pub fn mean<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	annotation: A,
	sum: &pixel::AllocatedPixel<E>,
	sum_64: u64,
	num_elems: usize,
) -> Result<pixel::AllocatedPixel<E>, SynthesisError>
where
	A: FnOnce() -> AR,
	AR: Into<String>,
{
	let num_samples = pixel::AllocatedPixel::alloc(cs.namespace(|| "mean"), || {
		let value: E::Fr = (E::Fr::from_repr((num_elems as u64).into())).unwrap();
		Ok(value)
	})?;
	
	let mean_int_var = pixel::AllocatedPixel::alloc(cs.namespace(|| "quotient"), || {
		let mean_val: u64 = sum_64 / num_elems as u64;//sum.get_value();
		let value: E::Fr = (E::Fr::from_repr(mean_val.into())).unwrap();
		Ok(value)
	})?;
	

	let mean_rem = pixel::AllocatedPixel::alloc(cs.namespace(|| "rem"), || {
		let mean_rem: u64 = sum_64 % num_elems as u64;//sum.get_value();
		let value: E::Fr = (E::Fr::from_repr(mean_rem.into())).unwrap();
		Ok(value)
	})?;
	
	mean_enforce(cs, || "mean enforce", &sum, &num_samples, &mean_int_var, &mean_rem);

	Ok(mean_int_var)
}

/// Adds a constraint to CS, enforcing an equality relationship between the allocated numbers a and b.
///
/// a == b
#[allow(dead_code)]
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
/// 
#[allow(dead_code)]
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
#[allow(dead_code)]
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
#[allow(dead_code)]
pub fn diff_sq_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
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
#[allow(dead_code)]
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
#[allow(dead_code)]
pub fn diff_mul_enforce<E: Engine, A, AR, CS: ConstraintSystem<E>>(
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
#[allow(dead_code)]
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
			&mean_a
				.get_value()
				.ok_or_else(|| SynthesisError::AssignmentMissing)?,
		);
		let mut tmpb = b
			.get_value()
			.ok_or_else(|| SynthesisError::AssignmentMissing)?;
		tmpb.sub_assign(
			&mean_b
				.get_value()
				.ok_or_else(|| SynthesisError::AssignmentMissing)?,
		);
		let mut tmp = tmpa;
		tmp.mul_assign(&tmpb);
		Ok(tmp)
	})?;
	// ()a - mean_a) * ()b - bmean) = res
	diff_mul_enforce(
		&mut cs,
		|| "diffsq constraint",
		&a,
		&mean_a,
		&b,
		&mean_b,
		&res,
	);

	Ok(res)
}
pub fn variance<E: Engine, A, AR, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	annotation: A,
	a: &Vec<pixel::AllocatedPixel<E>>,
	b: &Vec<pixel::AllocatedPixel<E>>,
	mean_a: &pixel::AllocatedPixel<E>,
	mean_b: &pixel::AllocatedPixel<E>,
) -> Result<pixel::AllocatedPixel<E>, SynthesisError>
where
	A: FnOnce() -> AR,
	AR: Into<String>,
{
	let mb_size = a.len();
	let mut varDiffSqMeanSrc: pixel::AllocatedPixel<E>;
	let mut vecADiffMul: Vec<_> = Vec::new();
	// sum diffsq src
	for i in 0..mb_size {
		let mut cs = cs.namespace(|| format!("diffsq {}", i));
		let value_num = diffmul(cs, &a[i], &mean_b, &b[i], &mean_b)?;
		vecADiffMul.push(value_num);
	}

	let num_value = pixel::AllocatedPixel::alloc(cs.namespace(|| "sum var"), || {
		let mut value = E::Fr::zero();
		for i in 0..mb_size {
			let pix = vecADiffMul[i].get_value();
			value.add_assign(&pix.unwrap());
		}
		Ok(value)
	})?;

	let res = sum_vec(cs, || format!("sum src"), &vecADiffMul).unwrap();

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
	use super::pixel::*;
	use super::ssim_circuit_proof_verify;
	use super::{mean, sum_vec, diffsq};
	use bellperson::{ConstraintSystem, SynthesisError};
	use ff::{BitIterator, Field, PrimeField};
	use fil_sapling_crypto::circuit::boolean::{self, AllocatedBit, Boolean};
	use paired::bls12_381::{Bls12, Fr};
	use rand::{Rand, Rng, SeedableRng, XorShiftRng};
	use storage_proofs::circuit::test::*;
	use paired::Engine;
	
	fn gen_sample<E: Engine, A, AR>(cs: &mut TestConstraintSystem<E>, annotation: A, ) -> Vec<AllocatedPixel<E>> 
	where
	A: FnOnce() -> AR,
	AR: Into<String>, 
	AR: Into<String>, {
		// Prepare 3x3 test vector

		let mut var_pix3x3: Vec<AllocatedPixel<E>> = Vec::new();
		for i in 0..9 {
			let mut cs = cs.namespace(|| format!("src {}", i));

			let value_num = AllocatedPixel::alloc(cs.namespace(|| format!("val {}", i)), || {
				let mut value = E::Fr::from_str("3").unwrap();
				if i == 0  {
					value = E::Fr::from_str("4").unwrap();
				}
				Ok(value)
			});
			var_pix3x3.push(value_num.unwrap());
		}
		var_pix3x3
	}
/*
	#[test]
	fn test_diffsq(){
		let mut cs = TestConstraintSystem::<Bls12>::new();
		let a_value = Some(Fr::from_str("5").unwrap());
		let a = AllocatedPixel::alloc(cs.namespace(|| format!("val {}", 1)), || {
				a_value.ok_or_else(|| SynthesisError::AssignmentMissing)
			}).unwrap();
		let b_value = Some(Fr::from_str("3").unwrap());
		let b = AllocatedPixel::alloc(cs.namespace(|| format!("val {}", 2)), || {
				b_value.ok_or_else(|| SynthesisError::AssignmentMissing)
			}).unwrap();
		let var_diff = diffsq(cs, &a, &b);
		assert!(var_diff.unwrap().get_value().unwrap() == Fr::from_str("4").unwrap());	
	}

	#[test]
	fn test_sumvec() {
		let mut cs = TestConstraintSystem::<Bls12>::new();
		let var_pix3x3 = gen_sample(&mut cs);
		let sum = sum_vec(&mut cs, || "sum vec", &var_pix3x3);
		//print!("Pixel variable={:?}", sum.unwrap().get_variable());
		assert!(sum.unwrap().get_value().unwrap() == Fr::from_str("27").unwrap());
	}
	
*/	
/*
	#[test]
	fn test_mean_decoupled_from_sum() {
		let mut cs = TestConstraintSystem::<Bls12>::new();
		let var_sum = AllocatedPixel::alloc(cs.namespace(|| format!("sum")), || {
			let value = Some(Fr::from_str("28").unwrap());
			print!("sum = {:?}", value );
			value.ok_or_else(|| SynthesisError::AssignmentMissing)
		});
		let var_mean = mean(&mut cs, || "test mean", &var_sum.unwrap(), 28, 9);
		//print!("Pixel variable={:?}", sum.unwrap().get_variable());
		print!("Num inputs: {:?}\n", cs.num_inputs());
		print!("Num constraints: {:?}\n", cs.num_constraints());

		assert!(var_mean.unwrap().get_value().unwrap() == Fr::from_str("3").unwrap());
		assert!(cs.is_satisfied());
	}
*/	

/*
    #[test]
	fn test_mean() {
		let mut cs = TestConstraintSystem::<Bls12>::new();
		let var_pix3x3 = gen_sample(&mut cs);
		let var_sum = sum_vec(&mut cs, || "sum vec", &var_pix3x3).unwrap();
		print!("Num inputs: {:?}\n", cs.num_inputs());
		print!("Num constraints: {:?}\n", cs.num_constraints());		
		let var_mean = mean(&mut cs, || "test mean", &var_sum, 28, 9);
		//print!("Pixel variable={:?}", sum.unwrap().get_variable());
		print!("Num inputs: {:?}\n", cs.num_inputs());
		print!("Num constraints: {:?}\n", cs.num_constraints());

		assert!(var_mean.unwrap().get_value().unwrap() == Fr::from_str("3").unwrap());
		assert!(cs.is_satisfied());
	}
*/	
	#[test]
	fn test_lum_ssim() {
		let mut cs = TestConstraintSystem::<Bls12>::new();

		let var_src3x3 = gen_sample(&mut cs, || "src pix");
		let var_dst3x3 = gen_sample(&mut cs, || "dst pix");
		let var_sum_src = sum_vec(&mut cs, || "sum vec", &var_src3x3).unwrap();
		let var_sum_dst = sum_vec(&mut cs, || "dst vec", &var_dst3x3).unwrap();
		print!("Num inputs: {:?}\n", cs.num_inputs());
		print!("Num constraints: {:?}\n", cs.num_constraints());		
		let var_mean_src = mean(&mut cs, || "test src mean", &var_sum_src, 28, 9);
		let var_mean_dst = mean(&mut cs, || "test dst mean", &var_sum_dst, 28, 9);
		//print!("Pixel variable={:?}", sum.unwrap().get_variable());
		print!("Num inputs: {:?}\n", cs.num_inputs());
		print!("Num constraints: {:?}\n", cs.num_constraints());

		assert!(var_mean_src.unwrap().get_value().unwrap() == Fr::from_str("3").unwrap());
		assert!(cs.is_satisfied());
	}
	
	/*	#[test]
		fn test_ssim_circuit_proof_verify() {
			let _src_pixel: Vec<u32> = (0..256).map(|x| x).collect();
			let _dst_pixel: Vec<u32> = (0..256).map(|x| x).collect();
			ssim_circuit_proof_verify(_src_pixel, _dst_pixel);
		}
	*/
}
