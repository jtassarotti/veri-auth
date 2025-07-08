use vrf_wasm::ecvrf::{ECVRFKeyPair, ECVRFProof, ECVRFPublicKey};
use vrf_wasm::vrf::VRFKeyPair;
use vrf_wasm::rng::WasmRng;
use vrf_wasm::VRFProof;

#[ocaml::func]
#[ocaml::sig("unit -> (int array * int array)")]
pub fn getKeys() -> (Vec<u8>, Vec<u8>) {
    let mut rng = WasmRng::default();
    let keypair = ECVRFKeyPair::generate(&mut rng);
    let key_bytes = bincode::serialize(&keypair).unwrap();
    let public_key_bytes = bincode::serialize(&keypair.pk).unwrap();
    (key_bytes, public_key_bytes)
}

#[ocaml::func]
#[ocaml::sig("int array -> string -> string * int array")]
pub fn getProof(keys: Vec<u8>, input: &str) -> (String, Vec<u8>) {
    let keypair: ECVRFKeyPair = bincode::deserialize(&keys).unwrap();
    let (hash, proof) = keypair.output(input.as_bytes());
    let proof_bytes = bincode::serialize(&proof).unwrap();
    (hex::encode(hash), proof_bytes)
}

#[ocaml::func]
#[ocaml::sig("int array -> string -> int array -> bool")]
pub fn verifyProof(public_key_bytes: Vec<u8>, input: &str, proof_bytes: Vec<u8>) -> bool {
    let public_key: ECVRFPublicKey = bincode::deserialize(&public_key_bytes).unwrap();
    let proof: ECVRFProof = bincode::deserialize(&proof_bytes).unwrap();
    proof.verify(input.as_bytes(), &public_key).is_ok()
}

