# Zero Knowledge Proof of Storage for VideoCoin Network

Proof of Storage for VideoCoin is defined in  "Section 7.1.1 Proof of Retrievability" of VideoCoin whitepaper[1]. This module contains Rust language implementation of Proof of Retrievability. We use merkle tree based proof as  described in the VideoCoin white paper, but differs from the original proposal as outlined below:

* This implementation uses zero knowledge proofs based on zkSnarks. It basically contains a zkSnarks preprocessing circuit to construct and verify the Merkle tree based proofs. 
* Instead of using GOP based challenge sequences, the implementation uses pHash of a portion of each video frame in the stream as merkle tree leaf and constructs the merkle tree. 
* The prover (Storage/Transcode worker) generates and commits the merkle tree root for a given challenge in the form of a random offset in the frame. This random offset defines the offset for pHash region. The prover also provides merkle tree authentication path for a randomly chosen leaf (pHash).
* The verifier/validator verifies submitted proof, using it as input to the zkSnarks verification process along with previously committed merkle root and challenge(pHash of the leaf) as a public witness. The challenge originates form the client who requested the transcode/storage service (Alternately the challenge can be generated non-interactively)
 
## Circuit construction / Proof generation / Verification
These components are implemented in src/merkle_pot.rs. The implementation consists of circuit construction, proof generation  and verification functions. This implementation leverages rust implementation of zkSanrks protocol by zcash and uses libraries from zcash and/or filecoin blockchain repos.
Download the filecoin's rust-fil-proofs(https://github.com/filecoin-project/rust-fil-proofs) to the parent folder where this zkpost repo is downloaded. This implementation also depends on zcash libraries bellman, sapling-crypto (which are slightly modified by filecoin and renamed as bellperson and fil-sapling-crypto). These are automatically downloaded from crates.io along with other standard Rust libraries.
   
## pHash generation for portion of a frame
A lightweight pHash library based in rustdct. It is self contained code and does not depend on any exteranl pHash libraries.

## Extract sequence of regions from the transcoded stream
A light-weight ffmpeg application that extracts regions of  decoded frame. This appication directly uses libavfmt and libavcodec instead of using ffmpeg command-line interface. It performs the decoding, and extraction of the image area for calculating pHash.

## Comparison with Filecoin
Our implementation is a domain specific (for video compressed streams for known algorithms) and leverages structure in the video compression data and provides a simple, yet very robust proof-of-retrievability mechanism.

## Comparison with VideoCoin's Proof of Transcode
Proof-of-transcode being implemented for VideoCoin relies on tinyRAM based zkSnarks approach, where as Proof-of-storage uses gadget based approach and based on libraries being used in zcash, filecoin networks. As both are still in development and based on zkSnarks, they can provide a set of verification toos that can be used to replace existing transcode validation and provide a scalable alternative. 

## Status
Each software component listed above is implemented and being tested.

## Todo List:
* Separate implementation in to set-up, proof-generation and verification.
* Wrap verification code to mimic current VideoCoin transcode validator and test it
* Integration and testing

## Challenges:
VideoCoin blockchain uses precompiled contracts based on alt-bn256 curves  to support zkSnark proof-verification. Proof-of-storage implementation for VideoCoin is based on libraries using Jubjub/twisted Edwards curves. We need to extend VideoCoin blockchain to add new precompiled contracts (which requires go-videocoin calling external rust library) or run a oraclized verifier.

## Testing 
### SSIM

Download this repo, and filecoin repo as explained above. 

Setup (generation of CRS 
```
RUST_BACKTRACE=1 cargo run setup ssim_crs.dat
```
Extract macroblocks(Y or Luma) from source and transcoded streams using viddec/gen-hash. Run make before using the following command.
```
./viddec/gen-hash --frame 0 --macroblock 0 --input ~/test_20M.mp4 --output input1.json
```

Proof generation
```
RUST_BACKTRACE=1 cargo run genproof ssim_crs.dat ssim_proof.dat input1.json input2.json witness.dat
```
Verification
```
RUST_BACKTRACE=1 cargo run verify  ssim_crs.dat ssim_proof.dat witness.dat
```

## References:

1. VideoCoin - A Decentralized Video Encoding, Storage, and Content Distribution Network
https://storage.googleapis.com/videocoin-preico/VideoCoin-Whitepaper.pdf

2. Filecoin: A Decentralized Storage Network
https://filecoin.io/filecoin.pdf

3. Zcash Protocol Specification Version 2019.0.4 [Overwinter+Sapling]
https://raw.githubusercontent.com/zcash/zips/master/protocol/protocol.pdf

4. Bellman: zk-SNARKs in Rust
https://electriccoin.co/blog/bellman-zksnarks-in-rust/
