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
extern crate rustc_serialize;

use rand::{Rng, SeedableRng, XorShiftRng};
use ff::{Field, PrimeField, PrimeFieldDecodingError, PrimeFieldRepr};
use std::fs::File;
use std::io::prelude::*;
use std::io::Read;
use std::path::Path;
use std::env;
use std::time::{Duration, Instant};
use std::process;
use rustc_serialize::json::Json;
use rustc_serialize::json;

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


#[derive(RustcDecodable, RustcEncodable)]
#[derive(Clone)]
#[derive(Default)]
pub struct SampleMb {
	pixels: Vec<u16>,
}

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

fn setup(crs_path: String)
{	
	let now = Instant::now();

	let mut ssim= mb_ssim::SsimApp::default();
	let p = ssim.setup();
	let mut f = File::create(&crs_path).expect("faild to open ssim_crs.dat file");
	p.write(&mut f).expect("failed to write params to ssim_crs.dat");
	println!("Setup {}", now.elapsed().as_millis());
}

fn get_input_mb(input_file: String) -> Vec<u32>
{
	let mut file = File::open(input_file).expect("verify: faild to open input_file file");
	let mut data = String::new();
	file.read_to_string(&mut data).expect("verify: faild to read witness file");
	let sample_mb: SampleMb = json::decode(&data).unwrap();
	let pixels =  sample_mb.pixels.iter().map(|x| *x as u32).collect();
	pixels
}

fn genproof(
	crs_path: String, 
	proof_path: String, 
	input1_path: String, 
	input2_path: String, 
	witness_path: String,)
{	
	let now = Instant::now();

    let file_path = Path::new(&crs_path);

	let mut ssim= mb_ssim::SsimApp::default();
    let groth_params: Parameters<Bls12> = {
		let f = File::open(&crs_path).expect("failed to open rssim_crs.dat");
		Parameters::read(&f, false).expect("failed to read rssim_crs.dat")
	};
	
	let mb_size = 256;
	let mut rng = rand::thread_rng();
	let src_mb: Vec<u32> = get_input_mb(input1_path);
	let dst_mb: Vec<u32> = get_input_mb(input2_path);
		
	let witns = mb_ssim::gen_witness(&src_mb.clone(), &dst_mb.clone());
	let proof_start = Instant::now();		
	let proof = ssim.create_proof(&groth_params, src_mb, dst_mb, witns.clone());
	println!("Proof generation {}", now.elapsed().as_millis());

	// save proof to file
	let mut proof_f = File::create(&proof_path).expect("faild to create proof file");
	proof.write(&mut proof_f).expect("failed to serialize proof file");
	
	let mut witness_f = File::create(witness_path).expect("failed to create witness file");
    let witness_encoded = json::encode(&witns).unwrap();
    witness_f.write_all(witness_encoded.as_bytes());

	println!("ssim_num={:?} ssim_den={:?}", witns.ssim_numerator, witns.ssim_denom);
	println!("Load CRS + Proof generation {}", now.elapsed().as_millis());
}

fn get_witness(witness_path: String) -> Vec<u32> {
	// let decoded: TestStruct = json::decode(&encoded[..]).unwrap();
	let mut file = File::open(witness_path).expect("verify: faild to open witness file");
	let mut data = String::new();
	file.read_to_string(&mut data).expect("verify: faild to read witness file");
	//let witness_j = Json::from_str(&data).expect("verify: faild to parse witness");
	let witness: mb_ssim::Witness = json::decode(&data).unwrap();
	let mut selected_fields: Vec<u32> = vec![];
	selected_fields.push(witness.ssim_numerator);
	selected_fields.push(witness.ssim_denom);
	println!("witness {:?}", selected_fields);
	selected_fields
}

fn verify(crs_path: String, proof_path: String, witness_path: String,)
{
	let now = Instant::now();	

    let file_path = Path::new(&crs_path);
	let mut ssim= mb_ssim::SsimApp::default();
    let groth_params: Parameters<Bls12> = {
		let f = File::open(&crs_path).expect("failed to open rssim_crs.dat");
		Parameters::read(&f, false).expect("failed to read rssim_crs.dat")
	};
			
	let mut f = File::open(&proof_path).expect("faild to open ssim_proof.dat file");
	let proof: Proof<Bls12> = Proof::read(&mut f).expect("failed to read proof to file ssim_proof.dat");
	
	let pvk = prepare_verifying_key(&groth_params.vk);
	let public_inputs = get_witness(witness_path);
	let verify_start = Instant::now();	
	let res = ssim.verify_proof(&pvk, &proof, public_inputs).unwrap();
	println!("Verificaiton result = {:?}", res);
	println!("Only Verification {}", verify_start.elapsed().as_millis());	
	println!("Load Proof+Verification {}", now.elapsed().as_millis());	
}



fn gensample(mb_size: u32, sample1_file: String, sample2_file: String) 
{
	let mut rng = rand::thread_rng();
	
	let sample_mb1 = SampleMb{
						pixels: (0..mb_size).map(|x| (rng.gen::<u8>()) as u16).collect()
					 };
	let sample_mb2 = SampleMb{
						pixels: (0..mb_size).map(|x| (rng.gen::<u8>()) as u16).collect()
					 };
	
	let sample1_encoded = json::encode(&sample_mb1).unwrap();
    let mut sample1_f = File::create(&sample1_file).expect("faild to create input2 file");
	sample1_f.write_all(sample1_encoded.as_bytes());
	
	let sample2_encoded = json::encode(&sample_mb2).unwrap();
	let mut input2_f = File::create(&sample2_file).expect("faild to create input2 file");
	input2_f.write_all(sample2_encoded.as_bytes());	
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
			if args.len() >= 3 {
    			let crs_file = args[2].clone();
				setup(crs_file)
			} else {
				println!("zkptrans setup crs_file");
				process::exit(1);
			}			
		},
		"genproof" => {
			println!("genproof");
			if args.len() >= 7 {
    			let crs_file = args[2].clone();
				let proof_file = args[3].clone();
				let input1_file = args[4].clone();
				let input2_file = args[5].clone();
				let witness_file = args[6].clone();
				genproof(crs_file, proof_file, input1_file, input2_file, witness_file)
			} else {
				println!("zkptrans genproof crs_file proof_file input1_file input_2 file witness_file");
				process::exit(1);
			}

		},
		"verify" => {
			println!("verify");
			if args.len() >= 5 {
    			let crs_file = args[2].clone();
				let proof_file = args[3].clone();
				let witness_file = args[4].clone();
				verify(crs_file, proof_file, witness_file)
			} else {
				println!("zkptrans verify crs_file proof_file witness_file");
				process::exit(1);
			}
		},
		"gensample" => {
			println!("gensample");
			if args.len() >= 4 {
    			let input1 = args[2].clone();
				let input2 = args[3].clone();
				gensample(256, input1, input2)
			} else {
				println!("zkptrans gensample input1_file input2_file");
				process::exit(1);
			}
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