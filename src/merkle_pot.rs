extern crate bellperson;
extern crate fil_sapling_crypto;
extern crate paired;
extern crate pbr;
extern crate rand;
extern crate storage_proofs;

use bellperson::ConstraintSystem;
use bellperson::SynthesisError;
use bellperson::groth16::*;
use ff::Field;
use ff::PrimeField;
use fil_sapling_crypto::circuit::{num, boolean, pedersen_hash, multipack};
use fil_sapling_crypto::jubjub::{JubjubBls12, JubjubEngine, edwards::Point};
use paired::bls12_381::{Bls12, Fr, FrRepr};
use rand::{Rng, SeedableRng, XorShiftRng};

use storage_proofs::circuit;
use storage_proofs::test_helper::random_merkle_path;
use rand::thread_rng;

use storage_proofs::hasher::pedersen::{PedersenDomain, PedersenFunction, PedersenHasher};
use storage_proofs::merkle::{MerkleProof, MerkleTree};

use std::fs::File;
use std::io::stderr;
use std::path::Path;
use std::time::{Duration, Instant};

use bellperson::groth16::*;
use bellperson::Circuit;
use clap::{self, App, Arg, SubCommand};

use pbr::ProgressBar;

//use logging_toolkit::make_logger;
use slog::Logger;
use super::constraint;

//lazy_static! {
//    pub static ref SP_LOG: Logger = make_logger("storage-proofs");
//}

/// This is an instance of the `ParallelProofOfRetrievability` circuit.
///
/// # Public Inputs
///
/// This circuit expects the following public inputs.
///
/// * for i in 0..values.len()
///   * [0] - packed version of `value` as bits. (might be more than one Fr)
///   * [1] - packed version of the `is_right` components of the auth_path.
///   * [2] - the merkle root of the tree.
pub struct ProofOfRetrievability<'a, E: JubjubEngine> {
    /// Paramters for the engine.
    pub params: &'a E::Params,

    /// Pedersen commitment to the value.
    pub value: Option<E::Fr>,

    /// The authentication path of the commitment in the tree.
    #[allow(clippy::type_complexity)]
    pub auth_path: Vec<Option<(E::Fr, bool)>>,

    /// The root of the underyling merkle tree.
    pub root: Option<E::Fr>,
}

impl<'a, E: JubjubEngine> Circuit<E> for ProofOfRetrievability<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {

        let real_root_value = self.root;

        // Allocate the "real" root that will be exposed.
        let rt = num::AllocatedNum::alloc(cs.namespace(|| "root value"), || {
            real_root_value.ok_or(SynthesisError::AssignmentMissing)
        })?;


        let mut cs = cs.namespace(|| format!("por"));
        let params = self.params;
        let value = self.value;
        let auth_path = self.auth_path.clone();

        let value_num = num::AllocatedNum::alloc(cs.namespace(|| "value"), || {
            value.ok_or_else(|| SynthesisError::AssignmentMissing)
        })?;

        value_num.inputize(cs.namespace(|| "value num"))?;

        // This is an injective encoding, as cur is a
        // point in the prime order subgroup.
        let mut cur = value_num;

        let mut auth_path_bits = Vec::with_capacity(auth_path.len());

        // Ascend the merkle tree authentication path
        for (i, e) in auth_path.into_iter().enumerate() {
            let cs = &mut cs.namespace(|| format!("merkle tree hash {}", i));

            // Determines if the current subtree is the "right" leaf at this
            // depth of the tree.
            let cur_is_right = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| "position bit"),
                e.map(|e| e.1),
            )?);

            // Witness the authentication path element adjacent
            // at this depth.
            let path_element =
                num::AllocatedNum::alloc(cs.namespace(|| "path element"), || {
                    Ok(e.ok_or(SynthesisError::AssignmentMissing)?.0)
                })?;

            // Swap the two if the current subtree is on the right
            let (xl, xr) = num::AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of preimage"),
                &cur,
                &path_element,
                &cur_is_right,
            )?;

            // We don't need to be strict, because the function is
            // collision-resistant. If the prover witnesses a congruency,
            // they will be unable to find an authentication path in the
            // tree with high probability.
            let mut preimage = vec![];
            preimage.extend(xl.into_bits_le(cs.namespace(|| "xl into bits"))?);
            preimage.extend(xr.into_bits_le(cs.namespace(|| "xr into bits"))?);

            // Compute the new subtree value
            cur = pedersen_hash::pedersen_hash(
                cs.namespace(|| "computation of pedersen hash"),
                pedersen_hash::Personalization::MerkleTree(i),
                &preimage,
                params,
            )?
            .get_x()
            .clone(); // Injective encoding

            auth_path_bits.push(cur_is_right);
        }

        // allocate input for is_right auth_path
        multipack::pack_into_inputs(cs.namespace(|| "packed auth_path"), &auth_path_bits)?;

        {
            // Validate that the root of the merkle tree that we calculated is the same as the input.
            constraint::equal(&mut cs, || "enforce root is correct", &cur, &rt);
        }

        // Expose the root
        rt.inputize(cs.namespace(|| "root"))?;

        Ok(())
    }
}


/// Generate a unique cache path, based on the inputs.
fn get_cache_path(
    name: &str,
    version: usize,
) -> String {
    format!(
        "/tmp/filecoin-proofs-cache-{}-{}",
        name.to_ascii_lowercase(),
        version,
    )
}

lazy_static! {
    static ref JUBJUB_BLS_PARAMS: JubjubBls12 = JubjubBls12::new();
}

/// A trait that makes it easy to implement "Examples". These are really tunable benchmarking CLI tools.
pub trait PorApi<'a, C: Circuit<Bls12>>: Default {
	/// The name of the application. Used for identifying caches.
    fn name() -> String;

    /// Generate groth parameters
    fn generate_groth_params<R: Rng>(
        &mut self,
        _: &mut R,
        _: &'a <Bls12 as JubjubEngine>::Params,
        _: usize,
    ) -> Parameters<Bls12>;

    #[allow(clippy::too_many_arguments)]
    fn create_proof<R: Rng>(
        &mut self,
        rng: &mut R,
        engine_params: &'a <Bls12 as JubjubEngine>::Params,
        groth_params: &Parameters<Bls12>,
		auth_path: Vec<Option<(Fr, bool)>>,
		leaf: Fr,
		root: Fr,
    ) -> Proof<Bls12>;

    /// Verify the given proof, return `None` if not implemented.
    fn verify_proof(&mut self, _: &Proof<Bls12>, _: &PreparedVerifyingKey<Bls12>) -> Option<bool>;
}


struct MerklePorApp {
    auth_path: Vec<Option<(Fr, bool)>>,
    root: Fr,
    leaf: Fr,
}

impl Default for MerklePorApp {
    fn default() -> Self {
        MerklePorApp {
            auth_path: Vec::default(),
            leaf: Fr::zero(),
            root: Fr::zero(),
        }
    }
}

impl<'a> PorApi<'a, ProofOfRetrievability<'a, Bls12>> for MerklePorApp {
    fn name() -> String {
        "Multi-Challenge MerklePor".to_string()
    }

    fn generate_groth_params<R: Rng>(
        &mut self,
        rng: &mut R,
        jubjub_params: &JubjubBls12,
        tree_depth: usize
    ) -> Parameters<Bls12> {
        generate_random_parameters::<Bls12, _, _>(
            ProofOfRetrievability {
                params: jubjub_params,
                value: None,
                auth_path: vec![None; tree_depth],
                root: None,
            },
            rng,
        )
        .unwrap()
    }

    fn create_proof<R: Rng>(
        &mut self,
        rng: &mut R,
        engine_params: &'a JubjubBls12,
        groth_params: &Parameters<Bls12>,
		auth_path: Vec<Option<(Fr, bool)>>,
		leaf: Fr,
		root: Fr,
    ) -> Proof<Bls12> {
        //let (auth_path, leaf, root) = random_merkle_path(rng, tree_depth);
        self.root = root;
        self.leaf = leaf;
        self.auth_path =  auth_path.clone();

        let c = ProofOfRetrievability {
            params: engine_params,
            value: Some(self.leaf),
            auth_path: self.auth_path.clone(),
            root: Some(self.root),
        };

        // create groth16 proof
        create_random_proof(c, groth_params, rng).expect("failed to create proof")

    }

    fn verify_proof(
        &mut self,
        proof: &Proof<Bls12>,
        pvk: &PreparedVerifyingKey<Bls12>,
    ) -> Option<bool> {
        // -- generate public inputs

        let auth_path = self.auth_path.clone();

        // regen values, avoids storing
        let value = Some(&self.leaf);

        let mut expected_inputs: Vec<Fr>;

		let auth_path_bits: Vec<bool> = auth_path.iter().map(|p| p.unwrap().1).collect();        
		let packed_auth_path: Vec<Fr> =
                    multipack::compute_multipacking::<Bls12>(&auth_path_bits);

		let mut input = vec![*value.unwrap()];
        input.extend(packed_auth_path);
        expected_inputs = input;

        // add the root as the last one
        expected_inputs.push(self.root);

        // -- verify proof with public inputs
        Some(verify_proof(pvk, proof, &expected_inputs).expect("failed to verify proof"))
    }
}


fn work_groth(
    mut instance: MerklePorApp,
    tree_depth: usize,
	_auth_path: Vec<Option<(Fr, bool)>>,
	_leaf : Fr,
	_root: Fr,
) {
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //info!(SP_LOG, "tree_depth: {}", tree_depth; "target" => "config");

	let (auth_path, leaf, root) = (_auth_path, _leaf, _root);

    let start = Instant::now();
    let mut param_duration = Duration::new(0, 0);

    let name = MerklePorApp::name();

    // caching
    let p = get_cache_path(&name, 4);
    let cache_path = Path::new(&p);
    let groth_params: Parameters<Bls12> = if cache_path.exists() {
        //info!(SP_LOG, "reading groth params from cache: {:?}", cache_path; "target" => "params");
        let f = File::open(&cache_path).expect("failed to read cache");
        Parameters::read(&f, false).expect("failed to read cached params")
    } else {
        //info!(SP_LOG, "generating new groth params"; "target" => "params");
        let p = instance.generate_groth_params(
            rng,
            &JUBJUB_BLS_PARAMS,
            tree_depth
        );
        //info!(SP_LOG, "writing params to cache: {:?}", cache_path; "target" => "params");

        let mut f = File::create(&cache_path).expect("faild to open cache file");
        p.write(&mut f).expect("failed to write params to cache");

        p
    };

    //info!(SP_LOG, "generating verification key"; "target" => "params");
    let pvk = prepare_verifying_key(&groth_params.vk);

    param_duration += start.elapsed();

    let mut proof_vec = vec![];
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);


    proof_vec.truncate(0);

    // -- create proof

    let start = Instant::now();
    let proof = instance.create_proof(
        rng,
        &JUBJUB_BLS_PARAMS,
        &groth_params,
		auth_path.clone(),
		leaf,
		root,
    );
    proof.write(&mut proof_vec).expect("failed to serialize proof");
    total_proving += start.elapsed();
    // -- verify proof

    let start = Instant::now();

    if let Some(is_valid) = instance.verify_proof(&proof, &pvk) {
        assert!(is_valid, "failed to verify proof");
    }

    total_verifying += start.elapsed();


    // -- print statistics

    let proving_avg = total_proving;
    let proving_avg = f64::from(proving_avg.subsec_nanos()) / 1_000_000_000f64
        + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying;
    let verifying_avg = f64::from(verifying_avg.subsec_nanos()) / 1_000_000_000f64
        + (verifying_avg.as_secs() as f64);

    //info!(SP_LOG, "avg_proving_time: {:?} seconds", proving_avg; "target" => "stats");
    //info!(SP_LOG, "avg_verifying_time: {:?} seconds", verifying_avg; "target" => "stats");
    //info!(SP_LOG, "params_generation_time: {:?}", param_duration; "target" => "stats");
}

fn merkel_path(
	data: Vec<u64>,
) -> (Vec<Option<(Fr, bool)>>, Fr, Fr, usize) {
	let challenge_leaf_index = 3;
	let leaves: Vec<Fr> = data.iter().map(|x| (Fr::from_repr(FrRepr::from(*x as u64))).unwrap()).collect();
	let tree_depth = (leaves.len() as f64).log2().ceil() as usize;
	//let leaf = leaves[challenge_leaf_index];
	let merk_tree = MerkleTree::<PedersenDomain, PedersenFunction>::from_data(leaves);

    // generate merkle path for challenged node and parents

    let merk_proof =  MerkleProof::<PedersenHasher>::new_from_proof(&merk_tree.gen_proof(challenge_leaf_index));
    let auth_path = merk_proof.as_options();
	let root : Fr  = merk_tree.root().into();
	let leaf : Fr = merk_tree.read_at(challenge_leaf_index).into();

	(auth_path, leaf, root, tree_depth)
}


pub fn create_proof(data: Vec<u64>) {
    let instance = MerklePorApp::default();
	let (auth_path, leaf, root, tree_depth) = merkel_path(data);
	work_groth(instance, tree_depth, auth_path.clone(), leaf, root);
}
