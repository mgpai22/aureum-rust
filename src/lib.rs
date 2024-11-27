mod test_data;

extern crate alloc;
extern crate wee_alloc;

use cml_chain::{
    address::Address,
    assets::{AssetName, MultiAsset},
    plutus::{PlutusData, PlutusV1Script, PlutusV2Script, PlutusV3Script},
    transaction::{DatumOption, NativeScript, TransactionInput, TransactionOutput},
    Deserialize, Script, Value,
};
use cml_chain::{PolicyId, Serialize};
use cml_core::ordered_hash_map::OrderedHashMap;
use cml_crypto::{DatumHash, TransactionHash};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

use serde::{Deserialize as SerdeDeserialize, Serialize as SerdeSerialize};
use std::fmt::Debug;
use uplc::tx;

#[derive(SerdeSerialize, SerdeDeserialize, Debug)]
struct EvalError {
    error_type: String,
    budget: Budget,
    debug_trace: Vec<String>,
}

#[derive(SerdeSerialize, SerdeDeserialize, Debug)]
struct Budget {
    mem: u64,
    cpu: u64,
}

#[derive(SerdeSerialize, SerdeDeserialize, Debug)]
pub struct Utxo {
    pub address: String,
    pub tx_hash: String,
    pub output_index: u64,
    pub datum_hash: Option<String>,
    pub datum: Option<String>,
    pub script_ref: Option<ScriptRef>,
    pub assets: HashMap<String, u64>,
}

#[derive(SerdeSerialize, SerdeDeserialize, Debug)]
pub struct ScriptRef {
    pub script_type: ScriptType,
    pub script: String,
}

#[derive(SerdeSerialize, SerdeDeserialize, Debug)]
pub enum ScriptType {
    Native,
    PlutusV1,
    PlutusV2,
    PlutusV3,
}

#[derive(Error, Debug)]
pub enum ScriptError {
    #[error("Failed to parse hex: {0}")]
    HexParseError(String),
    #[error("Failed to decode CBOR: {0}")]
    CborDecodeError(String),
    #[error("Invalid script type")]
    InvalidScriptType,
    #[error("Address parsing error: {0}")]
    AddressError(String),
    #[error("Asset error: {0}")]
    AssetError(String),
}

pub fn utxo_to_transaction_input(utxo: &Utxo) -> Result<TransactionInput, ScriptError> {
    Ok(TransactionInput::new(
        TransactionHash::from_hex(&utxo.tx_hash)
            .map_err(|e| ScriptError::HexParseError(e.to_string()))?,
        utxo.output_index,
    ))
}

pub fn build_output(utxo: &Utxo) -> Result<TransactionOutput, ScriptError> {
    let address = Address::from_bech32(&utxo.address)
        .map_err(|e| ScriptError::AddressError(e.to_string()))?;

    let datum = build_datum(utxo)?;

    match &utxo.script_ref {
        Some(script_ref) => Ok(TransactionOutput::new(
            address,
            Value::zero(),
            datum,
            Some(to_script_ref(script_ref)?),
        )),
        None => Ok(TransactionOutput::new(address, Value::zero(), datum, None)),
    }
}

pub fn utxo_to_transaction_output(utxo: &Utxo) -> Result<TransactionOutput, ScriptError> {
    let mut output = build_output(utxo)?;
    output.set_amount(assets_to_value(&utxo.assets)?);
    Ok(output)
}

fn build_datum(utxo: &Utxo) -> Result<Option<DatumOption>, ScriptError> {
    if let Some(datum_hash) = &utxo.datum_hash {
        Ok(Some(DatumOption::new_hash(
            DatumHash::from_hex(datum_hash)
                .map_err(|e| ScriptError::HexParseError(e.to_string()))?,
        )))
    } else if let Some(datum) = &utxo.datum {
        let bytes = hex::decode(datum).map_err(|e| ScriptError::HexParseError(e.to_string()))?;
        Ok(Some(DatumOption::new_datum(
            PlutusData::from_cbor_bytes(&bytes)
                .map_err(|e| ScriptError::CborDecodeError(e.to_string()))?,
        )))
    } else {
        Ok(None)
    }
}

fn to_script_ref(script: &ScriptRef) -> Result<Script, ScriptError> {
    match script.script_type {
        ScriptType::Native => Ok(Script::new_native(
            NativeScript::from_cbor_bytes(
                &hex::decode(&script.script)
                    .map_err(|e| ScriptError::HexParseError(e.to_string()))?,
            )
            .map_err(|e| ScriptError::CborDecodeError(e.to_string()))?,
        )),
        ScriptType::PlutusV1 => {
            let encoded = apply_double_cbor_encoding(&script.script)?;
            Ok(Script::new_plutus_v1(PlutusV1Script::new(
                hex::decode(&encoded).map_err(|e| ScriptError::HexParseError(e.to_string()))?,
            )))
        }
        ScriptType::PlutusV2 => {
            let encoded = apply_double_cbor_encoding(&script.script)?;
            let bytes =
                hex::decode(&encoded).map_err(|e| ScriptError::HexParseError(e.to_string()))?;
            Ok(Script::new_plutus_v2(
                PlutusV2Script::from_cbor_bytes(&bytes)
                    .map_err(|e| ScriptError::CborDecodeError(e.to_string()))?,
            ))
        }
        ScriptType::PlutusV3 => {
            let encoded = apply_double_cbor_encoding(&script.script)?;
            let bytes =
                hex::decode(&encoded).map_err(|e| ScriptError::HexParseError(e.to_string()))?;
            Ok(Script::new_plutus_v3(
                PlutusV3Script::from_cbor_bytes(&bytes)
                    .map_err(|e| ScriptError::CborDecodeError(e.to_string()))?,
            ))
        }
    }
}

pub fn assets_to_value(assets: &HashMap<String, u64>) -> Result<Value, ScriptError> {
    let mut multi_asset = MultiAsset::new();
    let lovelace = assets.get("lovelace").copied().unwrap_or(0);

    // Get unique policy IDs
    let policies: HashSet<String> = assets
        .keys()
        .filter(|unit| *unit != "lovelace")
        .map(|unit| unit[..56].to_string())
        .collect();

    for policy in policies {
        let mut assets_value = OrderedHashMap::new();

        for (unit, amount) in assets.iter().filter(|(unit, _)| unit.starts_with(&policy)) {
            let asset_name_hex = &unit[56..];
            let asset_name = AssetName::new(
                hex::decode(asset_name_hex)
                    .map_err(|e| ScriptError::HexParseError(e.to_string()))?,
            )
            .map_err(|e| ScriptError::AssetError(e.to_string()))?;

            assets_value.insert(asset_name, *amount);
        }

        let policy_id =
            PolicyId::from_hex(&policy).map_err(|e| ScriptError::HexParseError(e.to_string()))?;

        multi_asset.insert(policy_id, assets_value);
    }

    Ok(Value::new(lovelace, multi_asset))
}

fn apply_double_cbor_encoding(hex_str: &str) -> Result<String, ScriptError> {
    let cbor_bytes = hex::decode(hex_str).map_err(|e| ScriptError::HexParseError(e.to_string()))?;

    let mut double_cbor_bytes = Vec::new();
    let mut cbor_encoder = pallas_codec::minicbor::Encoder::new(&mut double_cbor_bytes);

    cbor_encoder
        .bytes(&cbor_bytes)
        .map_err(|e| ScriptError::CborDecodeError(e.to_string()))?;

    Ok(hex::encode(double_cbor_bytes))
}

#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

#[no_mangle]
pub extern "C" fn eval_phase_two_raw(
    tx_ptr: u64,
    tx_len: u32,
    utxos_ptr: u64,
    utxos_len: u32,
    cost_mdls_ptr: u64,
    cost_mdls_len: u32,
    initial_budget_n: u64,
    initial_budget_d: u64,
    slot_config_x: u64,
    slot_config_y: u64,
    slot_config_z: u32,
) -> u64 {
    unsafe {
        let tx_bytes = std::slice::from_raw_parts(tx_ptr as *const u8, tx_len as usize);
        let cost_mdls =
            std::slice::from_raw_parts(cost_mdls_ptr as *const u8, cost_mdls_len as usize);

        let utxos_raw = std::slice::from_raw_parts(utxos_ptr as *const u8, utxos_len as usize);
        let utxos: Vec<(Vec<u8>, Vec<u8>)> = bincode::deserialize(utxos_raw).unwrap();

        match tx::eval_phase_two_raw(
            tx_bytes,
            &utxos,
            Some(cost_mdls),
            (initial_budget_n, initial_budget_d),
            (slot_config_x, slot_config_y, slot_config_z),
            false,
            |_| (),
        ) {
            Ok(result) => {
                // Success case - prefix with 0 byte and serialize as CBOR array
                let mut result_bytes = vec![0u8];
                result_bytes.extend(serde_cbor::to_vec(&result).unwrap());

                let result_ptr = alloc(result_bytes.len() as u32);
                std::ptr::copy_nonoverlapping(
                    result_bytes.as_ptr(),
                    result_ptr as *mut u8,
                    result_bytes.len(),
                );
                ((result_ptr as u64) << 32) | (result_bytes.len() as u64)
            }
            Err(e) => {
                // Error case - prefix with 1 byte and serialize structured error
                let error = match e {
                    tx::error::Error::RedeemerError { err, .. } => {
                        let (mem, cpu, trace) = match err.as_ref() {
                            tx::error::Error::Machine(_, budget, trace) => {
                                (budget.mem, budget.cpu, trace.clone())
                            }
                            _ => (0, 0, vec![]),
                        };

                        EvalError {
                            error_type: format!("{:?}", err),
                            budget: Budget {
                                mem: mem.try_into().unwrap(),
                                cpu: cpu.try_into().unwrap(),
                            },
                            debug_trace: trace,
                        }
                    }
                    other => EvalError {
                        error_type: format!("{:?}", other),
                        budget: Budget { mem: 0, cpu: 0 },
                        debug_trace: vec![],
                    },
                };

                let mut error_bytes = vec![1u8];
                error_bytes.extend(serde_cbor::to_vec(&error).unwrap());

                let error_ptr = alloc(error_bytes.len() as u32);
                std::ptr::copy_nonoverlapping(
                    error_bytes.as_ptr(),
                    error_ptr as *mut u8,
                    error_bytes.len(),
                );
                ((error_ptr as u64) << 32) | (error_bytes.len() as u64)
            }
        }
    }
}

#[no_mangle]
pub extern "C" fn alloc(size: u32) -> u64 {
    let vec: Vec<u8> = Vec::with_capacity(size as usize);
    let ptr = vec.as_ptr() as u64;
    std::mem::forget(vec);
    ptr
}

#[no_mangle]
pub unsafe extern "C" fn dealloc(ptr: u64, size: u32) {
    let _ = Vec::from_raw_parts(ptr as *mut u8, 0, size as usize);
}

pub fn encode_transaction_input(utxo: &Utxo) -> Result<Vec<u8>, ScriptError> {
    let input = utxo_to_transaction_input(utxo)?;
    Ok(input.to_cbor_bytes())
}

#[no_mangle]
pub extern "C" fn utxo_to_input_bytes(utxos_ptr: u64, utxos_len: u32) -> u64 {
    unsafe {
        let utxos_raw = std::slice::from_raw_parts(utxos_ptr as *const u8, utxos_len as usize);
        let utxo: Utxo = match serde_cbor::from_slice(utxos_raw) {
            Ok(u) => u,
            Err(e) => {
                eprintln!("Failed to deserialize UTXO: {}", e);
                return 0;
            }
        };

        match encode_transaction_input(&utxo) {
            Ok(bytes) => {
                let result_ptr = alloc(bytes.len() as u32);
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), result_ptr as *mut u8, bytes.len());
                ((result_ptr as u64) << 32) | (bytes.len() as u64)
            }
            Err(e) => {
                eprintln!("Failed to encode transaction input: {}", e);
                0
            }
        }
    }
}

#[no_mangle]
pub extern "C" fn utxo_to_output_bytes(utxos_ptr: u64, utxos_len: u32) -> u64 {
    unsafe {
        if utxos_ptr == 0 || utxos_len == 0 {
            eprintln!(
                "Invalid input parameters: ptr={}, len={}",
                utxos_ptr, utxos_len
            );
            return 0;
        }

        let result = {
            let utxos_raw = std::slice::from_raw_parts(utxos_ptr as *const u8, utxos_len as usize);

            let utxo: Utxo = match serde_cbor::from_slice(utxos_raw) {
                Ok(u) => u,
                Err(e) => {
                    eprintln!("Failed to deserialize UTXO: {}", e);
                    return 0;
                }
            };

            match utxo_to_transaction_output(&utxo) {
                Ok(output) => {
                    let bytes = output.to_cbor_bytes();
                    if bytes.is_empty() {
                        eprintln!("Generated empty output bytes");
                        return 0;
                    }

                    let result_ptr = alloc(bytes.len() as u32);
                    if result_ptr == 0 {
                        eprintln!("Failed to allocate result memory");
                        return 0;
                    }

                    let result_value = ((result_ptr as u64) << 32) | (bytes.len() as u64);

                    std::ptr::copy_nonoverlapping(
                        bytes.as_ptr(),
                        result_ptr as *mut u8,
                        bytes.len(),
                    );

                    result_value
                }
                Err(e) => {
                    eprintln!("Failed to encode transaction output: {}", e);
                    0
                }
            }
        };

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_transaction_input() {
        let utxo = Utxo {
            address: "addr_test1wqt7deyeecx5ly8jw78uy8vntf8funjuzvu79p5m4pcmr3c2qsz75".to_string(),
            tx_hash: "fc964987a23f3a58b92281bbad8eed7bbf572a43ed4f6993bb8aaf5786eba57e".to_string(),
            output_index: 0,
            datum_hash: None,
            datum: None,
            script_ref: None,
            assets: HashMap::new(),
        };

        let result = encode_transaction_input(&utxo);
        assert!(result.is_ok());
        let bytes = result.unwrap();

        assert_eq!(
            hex::encode(&bytes),
            "825820fc964987a23f3a58b92281bbad8eed7bbf572a43ed4f6993bb8aaf5786eba57e00"
        );

        let decoded =
            TransactionInput::from_cbor_bytes(&bytes).expect("Should decode successfully");
        assert_eq!(decoded.index, 0);
        assert_eq!(
            decoded.transaction_id.to_hex(),
            "fc964987a23f3a58b92281bbad8eed7bbf572a43ed4f6993bb8aaf5786eba57e"
        );
    }

    #[test]
    fn test_encode_transaction_output() {
        let mut assets = HashMap::new();
        assets.insert("lovelace".to_string(), 1599010);

        assets.insert(
            "0772b5199d4afeafa5a54967210c33ceb4393626fd8cbef7dc6fa53a50414c4d".to_string(),
            103433,
        );

        assets.insert(
                    "fd6ea8139626cbbd4fb9fb976e5012b350d57f5fbbf18387662c95967374616b655f73696e676c65746f6e".to_string(),
                    1,
                );

        let datum_hex = "d8799f190d69c249e5fb76a3286aa6c9b2011b0000019341dcd0ae5820f709a1f623a991ede466a13755a476db6b93e398e9703cb43b7b778fc1f5e710c24a021e19e0c9bab2400000ff".to_string();

        let utxo = Utxo {
            address: "addr_test1wqt7deyeecx5ly8jw78uy8vntf8funjuzvu79p5m4pcmr3c2qsz75".to_string(),
            tx_hash: "fc964987a23f3a58b92281bbad8eed7bbf572a43ed4f6993bb8aaf5786eba57e".to_string(),
            output_index: 0,
            datum_hash: None,
            datum: Some(datum_hex),
            script_ref: None,
            assets,
        };

        pub fn encode_transaction_output(utxo: &Utxo) -> Result<Vec<u8>, ScriptError> {
            let output = utxo_to_transaction_output(utxo)?;
            Ok(output.to_cbor_bytes())
        }

        let result = encode_transaction_output(&utxo);
        assert!(result.is_ok());
        let bytes = result.unwrap();

        assert_eq!(
            hex::encode(&bytes),
            "a300581d7017e6e499ce0d4f90f2778fc21d935a4e9e4e5c1339e2869ba871b1c701821a00186622a2581cfd6ea8139626cbbd4fb9fb976e5012b350d57f5fbbf18387662c9596a14f7374616b655f73696e676c65746f6e01581c0772b5199d4afeafa5a54967210c33ceb4393626fd8cbef7dc6fa53aa14450414c4d1a00019409028201d818584ad8799f190d69c249e5fb76a3286aa6c9b2011b0000019341dcd0ae5820f709a1f623a991ede466a13755a476db6b93e398e9703cb43b7b778fc1f5e710c24a021e19e0c9bab2400000ff"
        );
    }

    #[test]
    fn test_encode_transaction_output_2() {
        let mut assets = HashMap::new();
        assets.insert("lovelace".to_string(), 2000000);

        assets.insert(
            "fd6ea8139626cbbd4fb9fb976e5012b350d57f5fbbf18387662c95967374616b655f73696e676c65746f6e".to_string(),
            1,
        );

        assets.insert(
            "0772b5199d4afeafa5a54967210c33ceb4393626fd8cbef7dc6fa53a50414c4d".to_string(),
            102155,
        );

        let datum_hex = "d8799f190e95c24a063a8968895b95c6780b011b000001936164e1e6582088d51c97ad9e05a442a2c416c3be84cf2f182b8613dd9d56a3e882b6b5c96d62c24a021e19e0c9bab2400000ff".to_string();

        let utxo = Utxo {
            address: "addr_test1wqt7deyeecx5ly8jw78uy8vntf8funjuzvu79p5m4pcmr3c2qsz75".to_string(),
            tx_hash: "fc9ea44d1a31a867a4ac8516c41a91d11a9331e8a581b24ecf8759659c9711e0".to_string(),
            output_index: 1,
            datum_hash: None,
            datum: Some(datum_hex),
            script_ref: None,
            assets,
        };

        pub fn encode_transaction_output(utxo: &Utxo) -> Result<Vec<u8>, ScriptError> {
            let output = utxo_to_transaction_output(utxo)?;
            Ok(output.to_cbor_bytes())
        }

        let result = encode_transaction_output(&utxo);
        assert!(result.is_ok());
        let bytes = result.unwrap();

        assert_eq!(
            hex::encode(&bytes),
            "a300581d7017e6e499ce0d4f90f2778fc21d935a4e9e4e5c1339e2869ba871b1c701821a001e8480a2581c0772b5199d4afeafa5a54967210c33ceb4393626fd8cbef7dc6fa53aa14450414c4d1a00018f0b581cfd6ea8139626cbbd4fb9fb976e5012b350d57f5fbbf18387662c9596a14f7374616b655f73696e676c65746f6e01028201d818584bd8799f190e95c24a063a8968895b95c6780b011b000001936164e1e6582088d51c97ad9e05a442a2c416c3be84cf2f182b8613dd9d56a3e882b6b5c96d62c24a021e19e0c9bab2400000ff"
        );
    }
}
