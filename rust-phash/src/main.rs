// Copyright (c) 2015-2017 The `img_hash` Crate Developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// https://github.com/rust-lang/rust/issues/57533
#![allow(missing_docs)]

use rustdct::{DCTplanner, TransformType2And3};
use transpose::transpose;

use std::sync::Arc;
use rand::Rng;
extern crate rustc_serialize;
use rustc_serialize::json::Json;
use rustc_serialize::json;
use std::env;
use std::fs::File;
use std::io::Read;
use std::process;

const HASH_WIDTH: u32 = 8;
const HASH_HEIGHT: u32 = 8;

// we perform the DCT on an enlarged image
const DCT_WIDTH: u32 = 32;
const DCT_HEIGHT: u32 = 32;

#[derive(RustcDecodable, RustcEncodable)]
#[derive(Clone)]
#[derive(Default)]
pub struct SampleFrame {
	pixels: Vec<u32>,
}

pub struct DctCtxt {
    row_dct: Arc<dyn TransformType2And3<f32>>,
    col_dct: Arc<dyn TransformType2And3<f32>>,
    width: usize,
    height: usize,
}

impl DctCtxt {
    pub fn new(width: usize, height: usize) -> Self {
        let mut planner = DCTplanner::new();

        DctCtxt {
            row_dct: planner.plan_dct2(width),
            col_dct: planner.plan_dct2(height),
            width,
            height,
        }
    }

    pub fn width(&self) -> u32 {
        self.width as u32
    }

    pub fn height(&self) -> u32 {
        self.height as u32
    }

    /// Perform a 2D DCT on a 1D-packed vector with a given `width x height`.
    ///
    /// Assumes `packed_2d` is double-length for scratch space. Returns the vector truncated to
    /// `width * height`.
    ///
    /// ### Panics
    /// If `self.width * self.height * 2 != packed_2d.len()`
    pub fn dct_2d(&self, mut packed_2d: Vec<f32>) -> Vec<f32> {
        let Self { ref row_dct, ref col_dct, width, height } = *self;

        let trunc_len = width * height;
        assert_eq!(trunc_len * 2, packed_2d.len());

        {
            let (packed_2d, scratch) = packed_2d.split_at_mut(trunc_len);

            for (row_in, row_out) in packed_2d.chunks_mut(width)
                .zip(scratch.chunks_mut(width)) {
                row_dct.process_dct2(row_in, row_out);
            }

            transpose(scratch, packed_2d, width, height);

            for (row_in, row_out) in packed_2d.chunks_mut(height)
                .zip(scratch.chunks_mut(height)) {
                col_dct.process_dct2(row_in, row_out);
            }

            transpose(scratch, packed_2d, width, height);
        }

        packed_2d.truncate(trunc_len);
        packed_2d
    }
}

/// Crop the values off a 1D-packed 2D DCT.
///
/// Returns `packed` truncated to the premultiplied size, as determined by `rowstride`
///
/// Generic for easier testing
fn crop_2d_dct<T: Copy>(mut packed: Vec<T>, rowstride: usize, scale: usize) -> Vec<T> {
    // assert that the rowstride was previously multiplied by SIZE_MULTIPLIER
    assert_eq!(rowstride % scale, 0);
    assert!(rowstride / scale > 0, "rowstride cannot be cropped: {}", rowstride);

    let new_rowstride = rowstride / scale;

    for new_row in 0 .. packed.len() / (rowstride * scale) {
        let (dest, src) = packed.split_at_mut(new_row * new_rowstride + rowstride);
        let dest_start = dest.len() - new_rowstride;
        let src_start = new_rowstride * new_row;
        let src_end = src_start + new_rowstride;
        dest[dest_start..].copy_from_slice(&src[src_start..src_end]);
    }

    let new_len = packed.len() / (scale * scale);
    packed.truncate(new_len);

    packed
}

fn mean_hash_f32<'a>(luma: &'a [f32]) -> impl Iterator<Item = bool> + 'a {
    let mean = luma.iter().sum::<f32>() / luma.len() as f32;
    luma.iter().map(move |&x| x >= mean)
}

/// Interface for types used for storing hash data.
///
/// This is implemented for `Vec<u8>`, `Box<[u8]>` and arrays that are multiples/combinations of
/// useful x86 bytewise SIMD register widths (64, 128, 256, 512 bits).
///
/// Please feel free to open a pull request [on Github](https://github.com/abonander/img_hash)
/// if you need this implemented for a different array size.
pub trait HashBytes {
    /// Construct this type from an iterator of bytes.
    ///
    /// If this type has a finite capacity (i.e. an array) then it can ignore extra data
    /// (the hash API will not create a hash larger than this type can contain). Unused capacity
    /// **must** be zeroed.
    fn from_iter<I: Iterator<Item = u8>>(iter: I) -> Self where Self: Sized;

    /// Return the maximum capacity of this type, in bits.
    ///
    /// If this type has an arbitrary/theoretically infinite capacity, return `usize::max_value()`.
    fn max_bits() -> usize;

    /// Get the hash bytes as a slice.
    fn as_slice(&self) -> &[u8];
}

impl HashBytes for Box<[u8]> {
    fn from_iter<I: Iterator<Item = u8>>(iter: I) -> Self {
        // stable in 1.32, effectively the same thing
        // iter.collect()
        iter.collect::<Vec<u8>>().into_boxed_slice()
    }

    fn max_bits() -> usize {
        usize::max_value()
    }

    fn as_slice(&self) -> &[u8] { self }
}

impl HashBytes for Vec<u8> {
    fn from_iter<I: Iterator<Item=u8>>(iter: I) -> Self {
        iter.collect()
    }

    fn max_bits() -> usize {
        usize::max_value()
    }

    fn as_slice(&self) -> &[u8] { self }
}

macro_rules! hash_bytes_array {
    ($($n:expr),*) => {$(
        impl HashBytes for [u8; $n] {
            fn from_iter<I: Iterator<Item=u8>>(mut iter: I) -> Self {
                // optimizer should eliminate this zeroing
                let mut out = [0; $n];

                for (src, dest) in iter.by_ref().zip(out.as_mut()) {
                    *dest = src;
                }

                out
            }

            fn max_bits() -> usize {
                $n * 8
            }

            fn as_slice(&self) -> &[u8] { self }
        }
    )*}
}

hash_bytes_array!(8, 16, 24, 32, 40, 48, 56, 64);

struct BoolsToBytes<I> {
    iter: I,
}

impl<I> Iterator for BoolsToBytes<I> where I: Iterator<Item=bool> {
    type Item = u8;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        // starts at the LSB and works up
        self.iter.by_ref().take(8).enumerate().fold(None, |accum, (n, val)| {
            accum.or(Some(0)).map(|accum| accum | ((val as u8) << n))
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lower, upper) = self.iter.size_hint();
        (
            lower / 8,
            // if the upper bound doesn't evenly divide by `8` then we will yield an extra item
            upper.map(|upper| if upper % 8 == 0 { upper / 8 } else { upper / 8 + 1})
        )
    }
}

pub(crate) trait BitSet: HashBytes {
    fn from_bools<I: Iterator<Item = bool>>(iter: I) -> Self where Self: Sized {
        Self::from_iter(BoolsToBytes { iter })
    }

    fn hamming(&self, other: &Self) -> u32 {
        self.as_slice().iter().zip(other.as_slice()).map(|(l, r)| (l ^ r).count_ones()).sum()
    }
}

struct T();
impl<T: HashBytes> BitSet for T {}

#[test]
fn test_crop_2d_dct() {
    let packed: Vec<i32> = (0 .. 64).collect();
    assert_eq!(
        crop_2d_dct(packed.clone(), 8, 2),
        [
            0, 1, 2, 3, // 4, 5, 6, 7
            8, 9, 10, 11, // 12, 13, 14, 15
            16, 17, 18, 19, // 20, 21, 22, 23,
            24, 25, 26, 27, // 28, 29, 30, 31,
            // 32 .. 64
        ]
    );
}

#[test]
fn test_dct_2d() {
    let dct_width = DCT_WIDTH;
    let dct_height = DCT_HEIGHT;
    let ctx = DctCtxt::new(dct_width as usize, dct_height as usize);
    let input_len: usize = (dct_width * dct_height) as usize;
    let mut vals_with_scratch: Vec<f32> = Vec::with_capacity((input_len * 2) as usize);
    vals_with_scratch.extend((0..input_len * 2).map (|val| {
        val as f32
    }));
    let dct_vals = ctx.dct_2d(vals_with_scratch);
    println!("dct len={} {:?}", dct_vals.len(), dct_vals);
}

fn gen_phash_multiple_frames_from_file(
	input_path: String) -> Vec<SampleFrame> 
{	
	let mut file = File::open(input_path).expect("verify: faild to open input_file");

	let mut data = String::new();
	file.read_to_string(&mut data).expect("verify: faild to read witness file");
    let frames:  Vec<SampleFrame> = json::decode(&data).unwrap();
    frames
}

pub fn main()
{
    let args: Vec<String> = env::args().collect();
	println!("{:?}", args);
	let mut cmd: String = "None".to_string();
	if args.len() > 1 {
    	cmd = args[1].clone();
	}
	match cmd.as_ref() {
		"file" => {
			println!("file");
			if args.len() >= 3 {
                let input_file = args[2].clone();
                let output_file = args[2].clone();
                let frames = gen_phash_multiple_frames_from_file(input_file);
                for frame in frames {
                    let frame_f: Vec<f32>  = frame.pixels.iter().map(|x| *x as f32).collect();
                    //println!("frame={:?}", frame_f);
                    let dct_width: u32 = DCT_WIDTH;
                    let dct_height: u32 = DCT_HEIGHT;
                    let input_len: usize = (dct_width * dct_height) as usize;

                    let ctx = DctCtxt::new(dct_width as usize, dct_height as usize);
                
                    let mut vals_with_scratch = Vec::with_capacity(input_len * 2);
                    vals_with_scratch.extend(frame_f.iter().map(|&val| {
                        val
                    }));

                    vals_with_scratch.extend(frame_f.iter().map(|&val| {
                        val
                    }));

                    let dct_vals = ctx.dct_2d(vals_with_scratch);
                    //println!("dct len={} {:?}", dct_vals.len(), dct_vals);
                    let cropped_dct =crop_2d_dct(dct_vals, DCT_WIDTH as usize, 4);
                    //println!("cropped dct: len={} {:?}", cropped_dct.len(), cropped_dct);
                    let hash: Vec<u8> = BitSet::from_bools(mean_hash_f32(&cropped_dct));
                    println!("hash: len={} {:?}", hash.len(), hash);
                }
			} else {
				println!("rust-phash input_file output_file");
				process::exit(1);
			}			
        },
		_ => println!("Unknown command\n "),
	}        
 /*
    let mut rng = rand::thread_rng();
    let dct_width: u32 = DCT_WIDTH;
    let dct_height: u32 = DCT_HEIGHT;
    let input_len: usize = (dct_width * dct_height) as usize;
    let mut data: Vec<f32> = Vec::new();
    for i in 0..input_len * 2 {
        data.push(rng.gen::<f32>());
    }
    let ctx = DctCtxt::new(dct_width as usize, dct_height as usize);

    let mut vals_with_scratch = Vec::with_capacity(input_len * 2);
    vals_with_scratch.extend(data.iter().map(|&val| {
        val
    }));
    let dct_vals = ctx.dct_2d(vals_with_scratch);
    println!("dct len={} {:?}", dct_vals.len(), dct_vals);
    let cropped_dct =crop_2d_dct(dct_vals, DCT_WIDTH as usize, 4);
    println!("cropped dct: len={} {:?}", cropped_dct.len(), cropped_dct);
    let hash: Vec<u8> = BitSet::from_bools(mean_hash_f32(&cropped_dct));
    println!("hash: len={} {:?}", hash.len(), hash);
 */ 
}