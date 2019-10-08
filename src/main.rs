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
use std::fs::File;
use std::path::Path;
use std::env;
use std::time::{Duration, Instant};

//mod macroblock;
mod pixel;
mod mb_ssim;
mod merkle_pot;
mod constraint;

use paired::bls12_381::{Bls12, Fr, FrRepr};

// For Testing
use storage_proofs::hasher::pedersen::{PedersenDomain, PedersenFunction, PedersenHasher};
use storage_proofs::merkle::{MerkleProof, MerkleTree};
use bellperson::groth16::{Parameters, prepare_verifying_key, Proof};
use mb_ssim::SsimApi;

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

fn setup()
{	
	let now = Instant::now();
	let crs_path: String = "ssim_crs.dat".to_string();

	let mut ssim= mb_ssim::SsimApp::default();
	let p = ssim.setup();
	let mut f = File::create(&crs_path).expect("faild to open ssim_crs.dat file");
	p.write(&mut f).expect("failed to write params to ssim_crs.dat");
	println!("Setup {}", now.elapsed().as_millis());
}

fn genproof()
{	
	let now = Instant::now();
	let crs_path: String = "ssim_crs.dat".to_string();
    let file_path = Path::new(&crs_path);
	let mut ssim= mb_ssim::SsimApp::default();
    let groth_params: Parameters<Bls12> = {
		let f = File::open(&crs_path).expect("failed to open rssim_crs.dat");
		Parameters::read(&f, false).expect("failed to read rssim_crs.dat")
	};
	
	let mb_size = 256;
	let mut rng = rand::thread_rng();
	let src_mb: Vec<u32> = (0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
	let dst_mb: Vec<u32> = (0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
		
	let witns = mb_ssim::gen_witness(&src_mb.clone(), &dst_mb.clone());
	let proof_start = Instant::now();		
	let proof = ssim.create_proof(&groth_params, src_mb, dst_mb, witns);
	println!("Proof generation {}", now.elapsed().as_millis());
/*	let mut proof_vec = vec![];
	proof_vec.truncate(0);
	proof.write(&mut proof_vec).expect("failed to serialize proof");
	println!("Proof len={:?} bytes={:?}", proof_vec.len(), proof_vec);
*/	
	// save to file
	let proof_path: String = "ssim_proof.dat".to_string();
	let mut f = File::create(&proof_path).expect("faild to open ssim_proof.dat file");
	proof.write(&mut f).expect("failed to serialize proof to file ssim_proof.dat");
	
	println!("Load CRS + Proof generation {}", now.elapsed().as_millis());
}

fn verify()
{
	let now = Instant::now();	
	let crs_path: String = "ssim_crs.dat".to_string();
    let file_path = Path::new(&crs_path);
	let mut ssim= mb_ssim::SsimApp::default();
    let groth_params: Parameters<Bls12> = {
		let f = File::open(&crs_path).expect("failed to open rssim_crs.dat");
		Parameters::read(&f, false).expect("failed to read rssim_crs.dat")
	};
	
	let mb_size = 256;
	let mut rng = rand::thread_rng();
	let src_mb: Vec<u32> = (0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
	let dst_mb: Vec<u32> = (0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
		
	let witns = mb_ssim::gen_witness(&src_mb.clone(), &dst_mb.clone());
	
	// read from file
	
	let proof_path: String = "ssim_proof.dat".to_string();
	let mut f = File::open(&proof_path).expect("faild to open ssim_proof.dat file");
	let proof: Proof<Bls12> = Proof::read(&mut f).expect("failed to read proof to file ssim_proof.dat");
	
	let pvk = prepare_verifying_key(&groth_params.vk);
	let public_inputs = vec![];
	let verify_start = Instant::now();	
	let res = ssim.verify_proof(&pvk, &proof, public_inputs).unwrap();
	println!("Verificaiton result = {:?}", res);
	println!("Only Verification {}", verify_start.elapsed().as_millis());	
	println!("Load Proof+Verification {}", now.elapsed().as_millis());	
}

fn main()
{
	let args: Vec<String> = env::args().collect();
	println!("{:?}", args);
	let mut cmd: String = "None".to_string();
	if args.len() > 1 {
    	cmd = args[1].clone();
	}
	
	match cmd.as_ref() {
		"setup" => {
			println!("Setup");
			setup();
		},
		"genproof" => {
			println!("genproof");
			genproof()
		},
		"verify" => {
			println!("verify");
			verify()
		},
		_ => println!("Unknown"),
	}
	//let src_mb: Vec<u32> = (0..256).map(|x| x).collect();
	//let dst_mb: Vec<u32> = (0..256).map(|x| x).collect();
	let mb_size = 256;
	let mut rng = rand::thread_rng();
	let src_mb: Vec<u32> = (0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
	let dst_mb: Vec<u32> = (0..mb_size).map(|x| (rng.gen::<u8>()) as u32).collect();
	
	//let _witns: mb_ssim::Witness = Default::default();		
	let witns = mb_ssim::gen_witness(&src_mb.clone(), &dst_mb.clone());
/*		
	mb_ssim::ssim_circuit_proof_verify(src_mb, dst_mb, witns);
*/

	
	let mut ssim= mb_ssim::SsimApp::default();
/*
	let p = ssim.setup(src_mb, dst_mb, witns);

	let mut f = File::create(&crs_path).expect("faild to open ssim_crs.dat file");
	p.write(&mut f).expect("failed to write params to ssim_crs.dat");
*/
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