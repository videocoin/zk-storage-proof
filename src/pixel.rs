extern crate fil_sapling_crypto;

use paired::Engine;

use ff::{BitIterator, Field, PrimeField, PrimeFieldRepr};

use bellperson::{ConstraintSystem, LinearCombination, SynthesisError, Variable};

use fil_sapling_crypto::circuit::boolean::{self, AllocatedBit, Boolean};

/// pixel.rs currently same as the following implementation. 
/// https://github.com/zcash-hackworks/sapling-crypto/blob/master/src/circuit/num.rs
/// It provides a gadget for  a number allocation (AllocatedNum) which encapsulates a constraint system variable and 
/// and addociated value (E::Fr) 
/// It is replicated here to allow customization and represent a pixel for VideoCoin proof-of-transcode
/// Traits that implement following methods:
/// 	alloc
/// 	inputize
/// 	into_bits_le_strict : Deconstructs this allocated number into its boolean representation 
/// 		in little-endian bitorder requiring that the representation strictly exists 
/// 		"in the field" (i.e., a congruency is not allowed.)
/// 	into_bits_le : 
/// 	mul
/// 	square
/// 	assert_nonzero
/// 	conditionally_reverse
/// 	get_value
/// 	get_variable
/// https://github.com/zcash-hackworks/sapling-crypto/blob/master/src/circuit/num.rs

pub struct AllocatedPixel<E: Engine> {
    pub value: Option<E::Fr>,
    pub variable: Variable,
}


trait Assignment<T> {
    fn get(&self) -> Result<&T, SynthesisError>;
}

impl<T> Assignment<T> for Option<T> {
    fn get(&self) -> Result<&T, SynthesisError> {
        match *self {
            Some(ref v) => Ok(v),
            None => Err(SynthesisError::AssignmentMissing),
        }
    }
}


impl<E: Engine> Clone for AllocatedPixel<E> {
    fn clone(&self) -> Self {
        AllocatedPixel {
            value: self.value,
            variable: self.variable,
        }
    }
}

impl<E: Engine> AllocatedPixel<E> {
    pub fn alloc<CS, F>(mut cs: CS, value: F) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        let mut new_value = None;
        let var = cs.alloc(
            || "pix",
            || {
                let tmp = value()?;
                new_value = Some(tmp);
                Ok(tmp)
            },
        )?;

        Ok(AllocatedPixel {
            value: new_value,
            variable: var,
        })
    }

    pub fn inputize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let input = cs.alloc_input(|| "input variable", || Ok(*self.value.get()?))?;

        cs.enforce(
            || "enforce input is correct",
            |lc| lc + input,
            |lc| lc + CS::one(),
            |lc| lc + self.variable,
        );

        Ok(())
    }

    /// Deconstructs this allocated number into its
    /// boolean representation in little-endian bit
    /// order, requiring that the representation
    /// strictly exists "in the field" (i.e., a
    /// congruency is not allowed.)
    pub fn into_bits_le_strict<CS>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        pub fn kary_and<E, CS>(
            mut cs: CS,
            v: &[AllocatedBit],
        ) -> Result<AllocatedBit, SynthesisError>
        where
            E: Engine,
            CS: ConstraintSystem<E>,
        {
            assert!(v.len() > 0);

            // Let's keep this simple for now and just AND them all
            // manually
            let mut cur = None;

            for (i, v) in v.iter().enumerate() {
                if cur.is_none() {
                    cur = Some(v.clone());
                } else {
                    cur = Some(AllocatedBit::and(
                        cs.namespace(|| format!("and {}", i)),
                        cur.as_ref().unwrap(),
                        v,
                    )?);
                }
            }

            Ok(cur.expect("v.len() > 0"))
        }

        // We want to ensure that the bit representation of a is
        // less than or equal to r - 1.
        let mut a = self.value.map(|e| BitIterator::new(e.into_repr()));
        let mut b = E::Fr::char();
        b.sub_noborrow(&1.into());

        let mut result = vec![];

        // Runs of ones in r
        let mut last_run = None;
        let mut current_run = vec![];

        let mut found_one = false;
        let mut i = 0;
        for b in BitIterator::new(b) {
            let a_bit = a.as_mut().map(|e| e.next().unwrap());

            // Skip over unset bits at the beginning
            found_one |= b;
            if !found_one {
                // a_bit should also be false
                a_bit.map(|e| assert!(!e));
                continue;
            }

            if b {
                // This is part of a run of ones. Let's just
                // allocate the boolean with the expected value.
                let a_bit = AllocatedBit::alloc(cs.namespace(|| format!("bit {}", i)), a_bit)?;
                // ... and add it to the current run of ones.
                current_run.push(a_bit.clone());
                result.push(a_bit);
            } else {
                if current_run.len() > 0 {
                    // This is the start of a run of zeros, but we need
                    // to k-ary AND against `last_run` first.

                    if last_run.is_some() {
                        current_run.push(last_run.clone().unwrap());
                    }
                    last_run = Some(kary_and(
                        cs.namespace(|| format!("run ending at {}", i)),
                        &current_run,
                    )?);
                    current_run.truncate(0);
                }

                // If `last_run` is true, `a` must be false, or it would
                // not be in the field.
                //
                // If `last_run` is false, `a` can be true or false.

                let a_bit = AllocatedBit::alloc_conditionally(
                    cs.namespace(|| format!("bit {}", i)),
                    a_bit,
                    &last_run.as_ref().expect("char always starts with a one"),
                )?;
                result.push(a_bit);
            }

            i += 1;
        }

        // char is prime, so we'll always end on
        // a run of zeros.
        assert_eq!(current_run.len(), 0);

        // Now, we have `result` in big-endian order.
        // However, now we have to unpack self!

        let mut lc = LinearCombination::zero();
        let mut coeff = E::Fr::one();

        for bit in result.iter().rev() {
            lc = lc + (coeff, bit.get_variable());

            coeff.double();
        }

        lc = lc - self.variable;

        cs.enforce(|| "unpacking constraint", |lc| lc, |lc| lc, |_| lc);

        // Convert into booleans, and reverse for little-endian bit order
        Ok(result.into_iter().map(|b| Boolean::from(b)).rev().collect())
    }

    /// Convert the allocated number into its little-endian representation.
    /// Note that this does not strongly enforce that the commitment is
    /// "in the field."
    pub fn into_bits_le<CS>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let bits = boolean::field_into_allocated_bits_le(&mut cs, self.value)?;

        let mut lc = LinearCombination::zero();
        let mut coeff = E::Fr::one();

        for bit in bits.iter() {
            lc = lc + (coeff, bit.get_variable());

            coeff.double();
        }

        lc = lc - self.variable;

        cs.enforce(|| "unpacking constraint", |lc| lc, |lc| lc, |_| lc);

        Ok(bits.into_iter().map(|b| Boolean::from(b)).collect())
    }

    pub fn mul<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut value = None;

        let var = cs.alloc(
            || "product num",
            || {
                let mut tmp = *self.value.get()?;
                tmp.mul_assign(other.value.get()?);

                value = Some(tmp);

                Ok(tmp)
            },
        )?;

        // Constrain: a * b = ab
        cs.enforce(
            || "multiplication constraint",
            |lc| lc + self.variable,
            |lc| lc + other.variable,
            |lc| lc + var,
        );

        Ok(AllocatedPixel {
            value: value,
            variable: var,
        })
    }

    pub fn square<CS>(&self, mut cs: CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut value = None;

        let var = cs.alloc(
            || "squared pix",
            || {
                let mut tmp = *self.value.get()?;
                tmp.square();

                value = Some(tmp);

                Ok(tmp)
            },
        )?;

        // Constrain: a * a = aa
        cs.enforce(
            || "squaring constraint",
            |lc| lc + self.variable,
            |lc| lc + self.variable,
            |lc| lc + var,
        );

        Ok(AllocatedPixel {
            value: value,
            variable: var,
        })
    }

    pub fn assert_nonzero<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let inv = cs.alloc(
            || "ephemeral inverse",
            || {
                let tmp = *self.value.get()?;

                if tmp.is_zero() {
                    Err(SynthesisError::DivisionByZero)
                } else {
                    Ok(tmp.inverse().unwrap())
                }
            },
        )?;

        // Constrain a * inv = 1, which is only valid
        // iff a has a multiplicative inverse, untrue
        // for zero.
        cs.enforce(
            || "nonzero assertion constraint",
            |lc| lc + self.variable,
            |lc| lc + inv,
            |lc| lc + CS::one(),
        );

        Ok(())
    }

    /// Takes two allocated numbers (a, b) and returns
    /// (b, a) if the condition is true, and (a, b)
    /// otherwise.
    pub fn conditionally_reverse<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        condition: &Boolean,
    ) -> Result<(Self, Self), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let c = Self::alloc(cs.namespace(|| "conditional reversal result 1"), || {
            if *condition.get_value().get()? {
                Ok(*b.value.get()?)
            } else {
                Ok(*a.value.get()?)
            }
        })?;

        cs.enforce(
            || "first conditional reversal",
            |lc| lc + a.variable - b.variable,
            |_| condition.lc(CS::one(), E::Fr::one()),
            |lc| lc + a.variable - c.variable,
        );

        let d = Self::alloc(cs.namespace(|| "conditional reversal result 2"), || {
            if *condition.get_value().get()? {
                Ok(*a.value.get()?)
            } else {
                Ok(*b.value.get()?)
            }
        })?;

        cs.enforce(
            || "second conditional reversal",
            |lc| lc + b.variable - a.variable,
            |_| condition.lc(CS::one(), E::Fr::one()),
            |lc| lc + b.variable - d.variable,
        );

        Ok((c, d))
    }

    pub fn get_value(&self) -> Option<E::Fr> {
		print!("pixel value {:?}\n", self.value);
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.variable
    }
}

#[cfg(test)]
mod test {
    use super::{AllocatedPixel, Boolean};
    use bellperson::ConstraintSystem;
    use storage_proofs::circuit::test::*;
    use ff::{BitIterator, Field, PrimeField};
    use paired::bls12_381::{Bls12, Fr};
    use rand::{Rand, Rng, SeedableRng, XorShiftRng};

	#[test]
	fn test_allocated_pixel() {
	    let mut cs = TestConstraintSystem::<Bls12>::new();
	
	    let value_pix = AllocatedPixel::alloc(&mut cs, || Ok(Fr::one())).unwrap();
		print!("Pixel variable={:?}", value_pix.get_variable());
	    assert!(cs.get("pix") == Fr::one());
		assert!(value_pix.get_value().unwrap() == Fr::one());
	}
    #[test]
    fn test_num_squaring() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedPixel::alloc(&mut cs, || Ok(Fr::from_str("3").unwrap())).unwrap();
        let n2 = n.square(&mut cs).unwrap();

        assert!(cs.is_satisfied());
        assert!(cs.get("squared pix") == Fr::from_str("9").unwrap());
        assert!(n2.value.unwrap() == Fr::from_str("9").unwrap());
        cs.set("squared pix", Fr::from_str("10").unwrap());
        assert!(!cs.is_satisfied());
    }	
    #[test]
    fn test_num_multiplication() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n =
            AllocatedPixel::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str("12").unwrap())).unwrap();
        let n2 =
            AllocatedPixel::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str("10").unwrap())).unwrap();
        let n3 = n.mul(&mut cs, &n2).unwrap();

		print!("Pixel n1={:?}:{:?} n2={:?}:{:?} n3={:?}:{:?}", n.get_variable(), n.get_value(), 
				n2.get_variable(),n2.get_value(), n3.get_variable(), n3.get_value());
        assert!(cs.is_satisfied());
        assert!(cs.get("product num") == Fr::from_str("120").unwrap());
        assert!(n3.value.unwrap() == Fr::from_str("120").unwrap());
        cs.set("product num", Fr::from_str("121").unwrap());
        assert!(!cs.is_satisfied());
    }
    #[test]
    fn test_num_conditional_reversal() {
        //let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedPixel::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str("1").unwrap())).unwrap();
            let b = AllocatedPixel::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str("2").unwrap())).unwrap();
            let condition = Boolean::constant(false);
            let (c, d) = AllocatedPixel::conditionally_reverse(&mut cs, &a, &b, &condition).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(a.value.unwrap(), c.value.unwrap());
            assert_eq!(b.value.unwrap(), d.value.unwrap());
        }

        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedPixel::alloc(cs.namespace(|| "a"), ||  Ok(Fr::from_str("1").unwrap())).unwrap();
            let b = AllocatedPixel::alloc(cs.namespace(|| "b"), ||  Ok(Fr::from_str("2").unwrap())).unwrap();
            let condition = Boolean::constant(true);
            let (c, d) = AllocatedPixel::conditionally_reverse(&mut cs, &a, &b, &condition).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(a.value.unwrap(), d.value.unwrap());
            assert_eq!(b.value.unwrap(), c.value.unwrap());
        }
    }
    #[test]
    fn test_into_bits() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        //for i in 0..200 
		{
            let r = Fr::rand(&mut rng);
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let n = AllocatedPixel::alloc(&mut cs, || Ok(r)).unwrap();
/*
            let bits = if i % 2 == 0 {
                n.into_bits_le(&mut cs).unwrap()
            } else {
                n.into_bits_le_strict(&mut cs).unwrap()
            };
*/
			let bits = n.into_bits_le(&mut cs).unwrap();
			
            assert!(cs.is_satisfied());

            for (b, a) in BitIterator::new(r.into_repr())
                .skip(1)
                .zip(bits.iter().rev())
            {
                if let &Boolean::Is(ref a) = a {
                    assert_eq!(b, a.get_value().unwrap());
                } else {
                    unreachable!()
                }
            }

            cs.set("pix", Fr::rand(&mut rng));
            assert!(!cs.is_satisfied());
            cs.set("pix", r);
            assert!(cs.is_satisfied());

            for i in 0..Fr::NUM_BITS {
                let name = format!("bit {}/boolean", i);
                let cur = cs.get(&name);
                let mut tmp = Fr::one();
                tmp.sub_assign(&cur);
                cs.set(&name, tmp);
                assert!(!cs.is_satisfied());
                cs.set(&name, cur);
                assert!(cs.is_satisfied());
            }
        }
    }
}
