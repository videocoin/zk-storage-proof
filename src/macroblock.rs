extern crate bellperson;
extern crate fil_sapling_crypto;
extern crate paired;
extern crate pbr;
extern crate rand;
extern crate storage_proofs;

use paired::Engine;
use bellperson::groth16::*;
use fil_sapling_crypto::circuit::multipack;
use fil_sapling_crypto::jubjub::JubjubBls12;
use paired::bls12_381::{Bls12, Fr};
use rand::Rng;

use storage_proofs::circuit;
use storage_proofs::example_helper::Example;
use storage_proofs::test_helper::random_merkle_path;

use super::pixel::AllocatedPixel;
use fil_sapling_crypto::circuit::boolean::{self, AllocatedBit, Boolean};
use bellperson::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use byteorder::{BigEndian, ByteOrder};
use std::collections::HashMap;
use std::fmt::Write;

use ff::{BitIterator, Field, PrimeField};

#[derive(Debug)]
enum NamedObject {
    Constraint(usize),
    Var(Variable),
    Namespace,
}

/// Constraint system for testing purposes.
pub struct TestConstraintSystem<E: Engine> {
    named_objects: HashMap<String, NamedObject>,
    current_namespace: Vec<String>,
    constraints: Vec<(
        LinearCombination<E>,
        LinearCombination<E>,
        LinearCombination<E>,
        String,
    )>,
    inputs: Vec<(E::Fr, String)>,
    aux: Vec<(E::Fr, String)>,
}
#[derive(Clone, Copy)]
struct OrderedVariable(Variable);

impl Eq for OrderedVariable {}
impl PartialEq for OrderedVariable {
    fn eq(&self, other: &OrderedVariable) -> bool {
        match (self.0.get_unchecked(), other.0.get_unchecked()) {
            (Index::Input(ref a), Index::Input(ref b)) => a == b,
            (Index::Aux(ref a), Index::Aux(ref b)) => a == b,
            _ => false,
        }
    }
}
impl PartialOrd for OrderedVariable {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for OrderedVariable {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.0.get_unchecked(), other.0.get_unchecked()) {
            (Index::Input(ref a), Index::Input(ref b)) => a.cmp(b),
            (Index::Aux(ref a), Index::Aux(ref b)) => a.cmp(b),
            (Index::Input(_), Index::Aux(_)) => Ordering::Less,
            (Index::Aux(_), Index::Input(_)) => Ordering::Greater,
        }
    }
}

fn proc_lc<E: Engine>(terms: &[(Variable, E::Fr)]) -> BTreeMap<OrderedVariable, E::Fr> {
    let mut map = BTreeMap::new();
    for &(var, coeff) in terms {
        map.entry(OrderedVariable(var))
            .or_insert(E::Fr::zero())
            .add_assign(&coeff);
    }

    // Remove terms that have a zero coefficient to normalize
    let mut to_remove = vec![];
    for (var, coeff) in map.iter() {
        if coeff.is_zero() {
            to_remove.push(var.clone())
        }
    }

    for var in to_remove {
        map.remove(&var);
    }

    map
}


fn eval_lc<E: Engine>(
    terms: &[(Variable, E::Fr)],
    inputs: &[(E::Fr, String)],
    aux: &[(E::Fr, String)],
) -> E::Fr {
    let mut acc = E::Fr::zero();

    for &(var, ref coeff) in terms {
        let mut tmp = match var.get_unchecked() {
            Index::Input(index) => inputs[index].0,
            Index::Aux(index) => aux[index].0,
        };

        tmp.mul_assign(&coeff);
        acc.add_assign(&tmp);
    }

    acc
}

impl<E: Engine> TestConstraintSystem<E> {
    pub fn new() -> TestConstraintSystem<E> {
        let mut map = HashMap::new();
        map.insert(
            "ONE".into(),
            NamedObject::Var(TestConstraintSystem::<E>::one()),
        );

        TestConstraintSystem {
            named_objects: map,
            current_namespace: vec![],
            constraints: vec![],
            inputs: vec![(E::Fr::one(), "ONE".into())],
            aux: vec![],
        }
    }

    pub fn pretty_print(&self) -> String {
        let mut s = String::new();

        let negone = {
            let mut tmp = E::Fr::one();
            tmp.negate();
            tmp
        };

        let powers_of_two = (0..E::Fr::NUM_BITS)
            .map(|i| E::Fr::from_str("2").unwrap().pow(&[i as u64]))
            .collect::<Vec<_>>();

        let pp = |s: &mut String, lc: &LinearCombination<E>| {
            write!(s, "(").unwrap();
            let mut is_first = true;
            for (var, coeff) in proc_lc::<E>(lc.as_ref()) {
                if coeff == negone {
                    write!(s, " - ").unwrap();
                } else if !is_first {
                    write!(s, " + ").unwrap();
                }
                is_first = false;

                if coeff != E::Fr::one() && coeff != negone {
                    for (i, x) in powers_of_two.iter().enumerate() {
                        if x == &coeff {
                            write!(s, "2^{} . ", i).unwrap();
                            break;
                        }
                    }

                    write!(s, "{} . ", coeff).unwrap();
                }

                match var.0.get_unchecked() {
                    Index::Input(i) => {
                        write!(s, "`{}`", &self.inputs[i].1).unwrap();
                    }
                    Index::Aux(i) => {
                        write!(s, "`{}`", &self.aux[i].1).unwrap();
                    }
                }
            }
            if is_first {
                // Nothing was visited, print 0.
                write!(s, "0").unwrap();
            }
            write!(s, ")").unwrap();
        };

        for &(ref a, ref b, ref c, ref name) in &self.constraints {
            write!(&mut s, "\n").unwrap();

            write!(&mut s, "{}: ", name).unwrap();
            pp(&mut s, a);
            write!(&mut s, " * ").unwrap();
            pp(&mut s, b);
            write!(&mut s, " = ").unwrap();
            pp(&mut s, c);
        }

        write!(&mut s, "\n").unwrap();

        s
    }


    pub fn which_is_unsatisfied(&self) -> Option<&str> {
        for &(ref a, ref b, ref c, ref path) in &self.constraints {
            let mut a = eval_lc::<E>(a.as_ref(), &self.inputs, &self.aux);
            let b = eval_lc::<E>(b.as_ref(), &self.inputs, &self.aux);
            let c = eval_lc::<E>(c.as_ref(), &self.inputs, &self.aux);

            a.mul_assign(&b);

            if a != c {
                return Some(&*path);
            }
        }

        None
    }

    pub fn is_satisfied(&self) -> bool {
        self.which_is_unsatisfied().is_none()
    }

    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    pub fn set(&mut self, path: &str, to: E::Fr) {
        match self.named_objects.get(path) {
            Some(&NamedObject::Var(ref v)) => match v.get_unchecked() {
                Index::Input(index) => self.inputs[index].0 = to,
                Index::Aux(index) => self.aux[index].0 = to,
            },
            Some(e) => panic!(
                "tried to set path `{}` to value, but `{:?}` already exists there.",
                path, e
            ),
            _ => panic!("no variable exists at path: {}", path),
        }
    }

    pub fn verify(&self, expected: &[E::Fr]) -> bool {
        assert_eq!(expected.len() + 1, self.inputs.len());

        for (a, b) in self.inputs.iter().skip(1).zip(expected.iter()) {
            if &a.0 != b {
                return false;
            }
        }

        return true;
    }

    pub fn num_inputs(&self) -> usize {
        self.inputs.len()
    }

    pub fn get_input(&mut self, index: usize, path: &str) -> E::Fr {
        let (assignment, name) = self.inputs[index].clone();

        assert_eq!(path, name);

        assignment
    }

    pub fn get(&mut self, path: &str) -> E::Fr {
        match self.named_objects.get(path) {
            Some(&NamedObject::Var(ref v)) => match v.get_unchecked() {
                Index::Input(index) => self.inputs[index].0,
                Index::Aux(index) => self.aux[index].0,
            },
            Some(e) => panic!(
                "tried to get value of path `{}`, but `{:?}` exists there (not a variable)",
                path, e
            ),
            _ => panic!("no variable exists at path: {}", path),
        }
    }

    fn set_named_obj(&mut self, path: String, to: NamedObject) {
        if self.named_objects.contains_key(&path) {
            panic!("tried to create object at existing path: {}", path);
        }

        self.named_objects.insert(path, to);
    }
}

fn compute_path(ns: &[String], this: String) -> String {
    if this.chars().any(|a| a == '/') {
        panic!("'/' is not allowed in names");
    }

    let mut name = String::new();

    let mut needs_separation = false;
    for ns in ns.iter().chain(Some(&this).into_iter()) {
        if needs_separation {
            name += "/";
        }

        name += ns;
        needs_separation = true;
    }

    name
}

impl<E: Engine> ConstraintSystem<E> for TestConstraintSystem<E> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.aux.len();
        let path = compute_path(&self.current_namespace, annotation().into());
        self.aux.push((f()?, path.clone()));
        let var = Variable::new_unchecked(Index::Aux(index));
        self.set_named_obj(path, NamedObject::Var(var));

        Ok(var)
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.inputs.len();
        let path = compute_path(&self.current_namespace, annotation().into());
        self.inputs.push((f()?, path.clone()));
        let var = Variable::new_unchecked(Index::Input(index));
        self.set_named_obj(path, NamedObject::Var(var));

        Ok(var)
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
    {
        let path = compute_path(&self.current_namespace, annotation().into());
        let index = self.constraints.len();
        self.set_named_obj(path.clone(), NamedObject::Constraint(index));

        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        self.constraints.push((a, b, c, path));
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        let name = name_fn().into();
        let path = compute_path(&self.current_namespace, name.clone());
        self.set_named_obj(path.clone(), NamedObject::Namespace);
        self.current_namespace.push(name);
    }

    fn pop_namespace(&mut self) {
        assert!(self.current_namespace.pop().is_some());
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

