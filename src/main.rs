#![allow(unused_imports)]
#![allow(unused_variables)]

#[macro_use]
extern crate failure;
#[macro_use]
extern crate lazy_static;
#[cfg(test)]
#[macro_use]
extern crate proptest;
#[macro_use]
extern crate clap;
#[macro_use]
extern crate slog;
#[macro_use]
extern crate serde;

extern crate bellperson;
extern crate paired;
extern crate pbr;
extern crate rand;
use rand::{Rng, SeedableRng, XorShiftRng};
use ff::{Field, PrimeField, PrimeFieldDecodingError, PrimeFieldRepr};

//mod macroblock;
mod pixel;
mod mb_ssim;
mod merkle_pot;
mod constraint;

use paired::bls12_381::{Bls12, Fr, FrRepr};

// For Testing
use storage_proofs::hasher::pedersen::{PedersenDomain, PedersenFunction, PedersenHasher};
use storage_proofs::merkle::{MerkleProof, MerkleTree};

fn merkel_path(
	data: Vec<u64>,
) -> (Vec<Option<(Fr, bool)>>, Fr, Fr, usize) {
	let challenge_leaf_index = 3;
	let leaves: Vec<Fr> = data.iter().map(|x| (Fr::from_repr(FrRepr::from(*x as u64))).unwrap()).collect();
	let tree_depth = (leaves.len() as f64).log2().ceil() as usize;
	let leaf = leaves[challenge_leaf_index];
	let merk_tree = MerkleTree::<PedersenDomain, PedersenFunction>::from_data(leaves);

    // generate merkle path for challenged node and parents
	println!("{:?}", merk_tree);
	println!("hash of uncle {:?}", merk_tree.read_at(2));
	println!("hash of leaf {:?}", merk_tree.read_at(3));
    let merk_proof =  MerkleProof::<PedersenHasher>::new_from_proof(&merk_tree.gen_proof(challenge_leaf_index));
	println!("merkel_proof {:?}", merk_proof);    
	let auth_path = merk_proof.as_options();
	let root : Fr  = merk_tree.root().into();
	
	println!("leaf {:?}", leaf);
	println!("root {:?}", root);
	for item in auth_path.clone() {
		println!("{:?}", item);
	}

	(auth_path, leaf, root, tree_depth)
}

fn main()
{
	//let src_mb: Vec<u32> = (0..256).map(|x| x).collect();
	//let dst_mb: Vec<u32> = (0..256).map(|x| x).collect();
	let mb_size = 256;
	let mut rng = rand::thread_rng();
	let src_mb: Vec<u32> = (0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
	let dst_mb: Vec<u32> = (0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
		
	//let _witns: mb_ssim::Witness = Default::default();		
	let witns = mb_ssim::gen_witness(&src_mb.clone(), &dst_mb.clone());
	mb_ssim::ssim_circuit_proof_verify(src_mb, dst_mb, witns);

/*
	let mut data:Vec<u64> = Vec::new();
	for i in 0..512 {
    	data.push(i);
	}
	let (auth_path, leaf, root, tree_depth) = merkel_path(data);

	let end = 0;
		
*/
/*
	let mut data:Vec<u64> = Vec::new();
	for i in 0..512 {
    	data.push(i);
	}
	merkle_pot::create_proof(data);
	let end = 0;*/
}