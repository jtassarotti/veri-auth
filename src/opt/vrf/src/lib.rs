use vrf_wasm::ecvrf::{ECVRFKeyPair, ECVRFProof, ECVRFPublicKey};
use vrf_wasm::vrf::VRFKeyPair;
use vrf_wasm::rng::WasmRng;
use vrf_wasm::VRFProof;

#[ocaml::func]
#[ocaml::sig("unit -> (int array * int array)")]
pub fn get_keys() -> (Vec<u8>, Vec<u8>) {
    let mut rng = WasmRng::default();
    let keypair = ECVRFKeyPair::generate(&mut rng);
    let key_bytes = bincode::serialize(&keypair).unwrap();
    let public_key_bytes = bincode::serialize(&keypair.pk).unwrap();
    (key_bytes, public_key_bytes)
}

#[ocaml::func]
#[ocaml::sig("int array -> string -> bytes * int array")]
pub fn randomize_string(keys: Vec<u8>, input: &str) -> ([u8; 64], Vec<u8>) {
    let keypair: ECVRFKeyPair = bincode::deserialize(&keys).unwrap();
    let (hash, proof) = keypair.output(input.as_bytes());
    let proof_bytes = bincode::serialize(&proof).unwrap();
    (hash, proof_bytes)
}

#[ocaml::func]
#[ocaml::sig("int array -> string -> int array -> bytes -> bool")]
pub fn verify_proof(public_key_bytes: Vec<u8>, input: &str, proof_bytes: Vec<u8>, hash: [u8; 64]) -> bool {
    let public_key: ECVRFPublicKey = bincode::deserialize(&public_key_bytes).unwrap();
    let proof: ECVRFProof = bincode::deserialize(&proof_bytes).unwrap();
    let comp_hash = ECVRFProof::to_hash(&proof);
    proof.verify(input.as_bytes(), &public_key).is_ok() && comp_hash == hash

}

