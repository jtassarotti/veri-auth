use vrf_wasm::ecvrf::{ECVRFKeyPair, ECVRFProof, ECVRFPrivateKey, ECVRFPublicKey};
use vrf_wasm::vrf::VRFKeyPair;
use vrf_wasm::rng::WasmRng;
use vrf_wasm::VRFProof;

#[ocaml::func]
#[ocaml::sig("unit -> (bytes * bytes)")]
pub fn get_keys() -> (Vec<u8>, Vec<u8>) {
    let mut rng = WasmRng::default();
    let keypair = ECVRFKeyPair::generate(&mut rng);
    let private_key_bytes = bincode::serialize(&keypair.sk).unwrap();
    let public_key_bytes = bincode::serialize(&keypair.pk).unwrap();
    (private_key_bytes, public_key_bytes)
}

#[ocaml::func]
#[ocaml::sig("bytes -> bytes -> bytes * bytes")]
pub fn prove(keys: Vec<u8>, input: &[u8]) -> ([u8; 64], Vec<u8>) {
    let private_key: ECVRFPrivateKey = bincode::deserialize(&keys).unwrap();
    let keypair: ECVRFKeyPair = ECVRFKeyPair::from(private_key);
    let (hash, proof) = keypair.output(input);
    let proof_bytes = bincode::serialize(&proof).unwrap();
    (hash, proof_bytes)
}

#[ocaml::func]
#[ocaml::sig("bytes -> bytes -> bytes")]
pub fn evaluate(keys: Vec<u8>, input: &[u8]) -> Vec<u8> {
    let private_key: ECVRFPrivateKey = bincode::deserialize(&keys).unwrap();
    let keypair: ECVRFKeyPair = ECVRFKeyPair::from(private_key);
    let proof = keypair.prove(input);
    bincode::serialize(&proof).unwrap()
}

#[ocaml::func]
#[ocaml::sig("bytes -> bytes -> bytes -> bytes -> bool")]
pub fn verify_proof(public_key_bytes: Vec<u8>, input: &[u8], proof_bytes: Vec<u8>, hash: [u8; 64]) -> bool {
    let public_key: ECVRFPublicKey = bincode::deserialize(&public_key_bytes).unwrap();
    let proof: ECVRFProof = bincode::deserialize(&proof_bytes).unwrap();
    let comp_hash = ECVRFProof::to_hash(&proof);
    proof.verify(input, &public_key).is_ok() && comp_hash == hash
}

#[ocaml::func]
#[ocaml::sig("bytes -> bytes -> bytes -> bool * bytes ")]
pub fn verify_proof2(public_key_bytes: Vec<u8>, input: &[u8], proof_bytes: Vec<u8>) -> (bool, [u8; 64]) {
    let public_key: ECVRFPublicKey = bincode::deserialize(&public_key_bytes).unwrap();
    let proof: ECVRFProof = bincode::deserialize(&proof_bytes).unwrap();
    let comp_hash = ECVRFProof::to_hash(&proof);
    (proof.verify(input, &public_key).is_ok(), comp_hash)
}

