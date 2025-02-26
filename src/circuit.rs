use ff::{PrimeField, PrimeFieldBits};
use nova::frontend::{
    num::AllocatedNum, AllocatedBit, ConstraintSystem, LinearCombination, SynthesisError,
};
use nova::nebula::rs::StepCircuit;

#[derive(Clone, Debug, Default)]
pub struct ProximityCircuit<F: PrimeField + PrimeFieldBits> {
    x: F,
    y: F,
}

impl<F: PrimeField + PrimeFieldBits> ProximityCircuit<F> {
    pub fn new(x: F, y: F) -> Self {
        Self { x, y }
    }
}

impl<F> StepCircuit<F> for ProximityCircuit<F>
where
    F: PrimeField + PrimeFieldBits,
{
    fn arity(&self) -> usize {
        1
    }
    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let x_ref = F::from(5000);
        let y_ref = F::from(5000);
        let radius = F::from(100);
        // the number of bits required to represent any number used: it is 2n + 1 where n is the number of bits required to represent the largest number
        // because we then compare the difference of the sum of squares with the square of the radius
        let num_bits = 13 * 2 + 1;

        let x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(self.x))?;
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(self.y))?;

        // check greater of x and x_ref to perform the subtraction
        let x_lt = less_than(&x, x_ref, num_bits, &mut cs.namespace(|| "x lt x_ref"))?;
        let y_lt = less_than(&y, y_ref, num_bits, &mut cs.namespace(|| "y lt y_ref"))?;

        // Calculate diff
        let x_diff = AllocatedNum::alloc(cs.namespace(|| "x_diff"), || {
            let x_value = x.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            if x_lt.get_value().ok_or(SynthesisError::AssignmentMissing)? {
                Ok(x_ref - x_value)
            } else {
                Ok(x_value - x_ref)
            }
        })?;

        let y_diff = AllocatedNum::alloc(cs.namespace(|| "y_diff"), || {
            let y_value = y.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            if y_lt.get_value().ok_or(SynthesisError::AssignmentMissing)? {
                Ok(y_ref - y_value)
            } else {
                Ok(y_value - y_ref)
            }
        })?;

        // Enforce diff calculation
        // ???

        // Check if point is within radius (x_diff^2 + y_diff^2 <= radius^2)
        // calculate x_diff^2 and y_diff^2
        let x_diff_squared = AllocatedNum::alloc(cs.namespace(|| "x_diff_squared"), || {
            let x_diff_value = x_diff
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(x_diff_value * x_diff_value)
        })?;

        let y_diff_squared = AllocatedNum::alloc(cs.namespace(|| "y_diff_squared"), || {
            let y_diff_value = y_diff
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(y_diff_value * y_diff_value)
        })?;

        cs.enforce(
            || "enforce x_diff_squared",
            |lc| lc + x_diff.get_variable(),
            |lc| lc + x_diff.get_variable(),
            |lc| lc + x_diff_squared.get_variable(),
        );

        cs.enforce(
            || "enforce y_diff_squared",
            |lc| lc + y_diff.get_variable(),
            |lc| lc + y_diff.get_variable(),
            |lc| lc + y_diff_squared.get_variable(),
        );

        let sum_squared = AllocatedNum::alloc(cs.namespace(|| "sum_squared"), || {
            let x_diff_squared_value = x_diff_squared
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            let y_diff_squared_value = y_diff_squared
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(x_diff_squared_value + y_diff_squared_value)
        })?;

        cs.enforce(
            || "enforce sum_squared",
            |lc| lc + x_diff_squared.get_variable() + y_diff_squared.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + sum_squared.get_variable(),
        );

        let radius_squared = radius * radius;

        let is_within_radius = less_than(
            &sum_squared,
            radius_squared,
            num_bits,
            &mut cs.namespace(|| "x_sq + y_sq lt r_sq"),
        )?;

        let output = AllocatedNum::alloc(cs.namespace(|| "output"), || {
            let is_within_radius_value = is_within_radius
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(if is_within_radius_value {
                F::from(1)
            } else {
                F::from(0)
            })
        })?;

        Ok(vec![output])
    }
    fn non_deterministic_advice(&self) -> Vec<F> {
        vec![]
    }
}

fn num_to_bits_le_bounded<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    n: AllocatedNum<F>,
    num_bits: u8,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let opt_bits = match n.get_value() {
        Some(v) => v
            .to_le_bits()
            .into_iter()
            .take(num_bits as usize)
            .map(Some)
            .collect::<Vec<Option<bool>>>(),
        None => vec![None; num_bits as usize],
    };

    // Add one witness per input bit in little-endian bit order
    let bits_circuit = opt_bits
        .into_iter()
        .enumerate()
        // AllocateBit enforces the value to be 0 or 1 at the constraint level
        .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("b_{}", i)), b).unwrap())
        .collect::<Vec<AllocatedBit>>();

    let mut weighted_sum_lc = LinearCombination::zero();
    let mut pow2 = F::ONE;

    for bit in bits_circuit.iter() {
        weighted_sum_lc = weighted_sum_lc + (pow2, bit.get_variable());
        pow2 = pow2.double();
    }

    cs.enforce(
        || "bit decomposition check",
        |lc| lc + &weighted_sum_lc,
        |lc| lc + CS::one(),
        |lc| lc + n.get_variable(),
    );

    Ok(bits_circuit)
}

/* fn get_msb_index<F: PrimeField + PrimeFieldBits>(n: F) -> u8 {
    n.to_le_bits()
        .into_iter()
        .enumerate()
        .rev()
        .find(|(_, b)| *b)
        .unwrap()
        .0 as u8
} */

fn less_than<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
    a: &AllocatedNum<F>,
    b: F,
    num_bits: u8,
    cs: &mut CS,
) -> Result<AllocatedBit, SynthesisError> {
    let shifted_diff = AllocatedNum::alloc(cs.namespace(|| "shifted_diff"), || {
        let a_value = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        Ok(a_value + F::from(1 << num_bits) - b)
    })?;

    cs.enforce(
        || "shifted_diff_computation",
        |lc| lc + a.get_variable() + (F::from(1 << num_bits) - b, CS::one()),
        |lc: LinearCombination<F>| lc + CS::one(),
        |lc| lc + shifted_diff.get_variable(),
    );

    let shifted_diff_bits = num_to_bits_le_bounded::<F, CS>(cs, shifted_diff, num_bits + 1)?;

    let output = AllocatedBit::alloc(cs.namespace(|| "output"), {
        Some(
            !shifted_diff_bits[num_bits as usize]
                .get_value()
                .unwrap_or(false),
        )
    })?;

    // would like to enforce shifted_diff_bits[num_bits as usize] == (1 - output), to ensure output is opposite of the MSB
    /*     cs.enforce(
        || "output_computation",
        |lc| lc + shifted_diff_bits[num_bits as usize].get_variable(),
        |lc: LinearCombination<F>| lc + CS::one(),
        |lc| lc + (F::ONE - output.get_variable(), CS::one()),
    ); */

    Ok(output)
}

#[cfg(test)]
mod tests {
    use crate::circuit::ProximityCircuit;
    use ff::Field;
    use halo2curves::bn256::{Bn256, Fr};
    use nova::{
        nebula::rs::{PublicParams, RecursiveSNARK},
        onchain::{decider::{prepare_calldata, Decider}, eth::evm::{compile_solidity, Evm}, utils::{get_formatted_calldata, get_function_selector_for_nova_cyclefold_verifier}, verifiers::{groth16::SolidityGroth16VerifierKey, kzg::SolidityKZGVerifierKey, nebula::{get_decider_template_for_cyclefold_decider, NovaCycleFoldVerifierKey}}},
        provider::{Bn256EngineKZG, GrumpkinEngine},
        traits::{snark::RelaxedR1CSSNARKTrait, Engine},
    };
    use rand::thread_rng;

    use std::time::Instant;

    #[test]
    fn test_all() {
        type E1 = Bn256EngineKZG;
        type E2 = GrumpkinEngine;
        type EE1 = nova::provider::hyperkzg::EvaluationEngine<Bn256, E1>;
        type EE2 = nova::provider::ipa_pc::EvaluationEngine<E2>;
        type S1 = nova::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
        type S2 = nova::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

        let mut rng = thread_rng();
        let circuit = ProximityCircuit {
            x: <E1 as Engine>::Scalar::from(5001u64),
            y: <E1 as Engine>::Scalar::from(5001u64),
        };

        // produce public parameters
        let rs_pp = PublicParams::<E1>::setup(&circuit.clone(), &*S1::ck_floor(), &*S2::ck_floor());

        let num_steps = 3;
        let mut ic_i = <E1 as Engine>::Scalar::ZERO;
        let z0 = vec![<E1 as Engine>::Scalar::ONE];
        // produce a recursive SNARK
        let mut rs = RecursiveSNARK::<E1>::new(&rs_pp, &circuit, &z0).unwrap();

        for i in 0..num_steps {
            let start = Instant::now();
            rs.prove_step(&rs_pp, &circuit, ic_i).unwrap();

            ic_i = rs.increment_commitment(&rs_pp, &circuit);
            println!("RecursiveSNARK::prove {} : took {:?} ", i, start.elapsed());
        }

        // verify the recursive SNARK
        let res = rs.verify(&rs_pp, num_steps, &z0, ic_i);
        assert!(res.is_ok());
        println!("RecursiveSNARK::verify: {:?}", res.is_ok(),);

        let zn = res.unwrap();

        // sanity: check the claimed output with a direct computation of the same
        assert_eq!(zn, vec![<E1 as Engine>::Scalar::ONE]);
        let start = Instant::now();
        // produce the prover and verifier keys for compressed snark
        let (decider_pk, decider_vk) = Decider::setup(&rs_pp, &mut rng, z0.len()).unwrap();
        println!("Decider::setup: took {:?}", start.elapsed());

        let start = Instant::now();
        // produce a compressed SNARK
        let res = Decider::prove(&rs_pp, &decider_pk, &rs, &mut rng);
        assert!(res.is_ok());
        let compressed_snark = res.unwrap();
        println!("Decider::prove: took {:?}", start.elapsed());

        let start = Instant::now();
        // verify the compressed SNARK
        let res = Decider::verify(
            &compressed_snark,
            decider_vk.clone()
        );
        assert!(res.is_ok());
        println!("Decider::verify: took {:?}", start.elapsed());

        // Now, let's generate the Solidity code that verifies this Decider final proof
        let function_selector =
            get_function_selector_for_nova_cyclefold_verifier(rs.z0.len() * 2 + 1);

        let calldata: Vec<u8> = prepare_calldata(
            function_selector,
            &compressed_snark,
        )
        .unwrap();

        // prepare the setup params for the solidity verifier
        let nova_cyclefold_vk = NovaCycleFoldVerifierKey::from((
            decider_vk.pp_hash,
            SolidityGroth16VerifierKey::from(decider_vk.groth16_vk),
            SolidityKZGVerifierKey::from((decider_vk.kzg_vk, Vec::new())),
            rs.z0.len(),
        ));

        // generate the solidity code
        let decider_solidity_code = get_decider_template_for_cyclefold_decider(nova_cyclefold_vk);

        // verify the proof against the solidity code in the EVM
        let nova_cyclefold_verifier_bytecode =
            compile_solidity(&decider_solidity_code, "NovaDecider");
        let mut evm = Evm::default();

        let verifier_address = evm.create(nova_cyclefold_verifier_bytecode);
        println!("verifier_address: {:?}", verifier_address);
        let (gas, output) = evm.call(verifier_address, calldata.clone());
        println!("Solidity::verify: {:?}, gas: {:?}", output, gas);
        assert_eq!(*output.last().unwrap(), 1);

        // save smart contract and the calldata
        println!("storing nova-verifier.sol and the calldata into files");
        use std::fs;
        fs::write(
            "./nova-verifier.sol",
            decider_solidity_code.clone(),
        )
        .expect("Unable to write to file");
        fs::write("./solidity-calldata.calldata", calldata.clone()).expect("");
        let s = get_formatted_calldata(calldata.clone());
        fs::write("./solidity-calldata.inputs", s.join(",\n")).expect("");
    }
}
