// dag-json serde Deserialize implementations
// Handles special dag-json encodings for binary data and CID links

use base64::{engine::general_purpose, Engine as _};
use serde::{Deserialize, Deserializer};
use serde_json::Value;

/// Deserialize dag-json binary encoding: {"/":{bytes":"<base64url>"}}
/// The bytes field contains base64url-encoded binary data.
pub fn deserialize_dag_binary<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
where
    D: Deserializer<'de>,
{
    let value = Value::deserialize(deserializer)?;

    // Check if it's a dag-json bytes object
    if let Value::Object(map) = &value
        && let Some(Value::Object(inner)) = map.get("/")
        && let Some(Value::String(base64_str)) = inner.get("bytes")
    {
        // Decode base64url (standard base64 with URL-safe alphabet)
        // Try URL_SAFE_NO_PAD first
        let result = general_purpose::URL_SAFE_NO_PAD.decode(base64_str);
        if result.is_ok() {
            return result.map_err(serde::de::Error::custom);
        }

        // If that fails, try adding padding and using URL_SAFE
        let padding = (4 - base64_str.len() % 4) % 4;
        let padded = format!("{}{}", base64_str, "=".repeat(padding));
        return general_purpose::URL_SAFE
            .decode(&padded)
            .or_else(|_| general_purpose::STANDARD.decode(&padded))
            .map_err(serde::de::Error::custom);
    }

    Err(serde::de::Error::custom("Expected dag-json bytes object"))
}

/// Deserialize dag-json CID link encoding: {"/":"<multibase-cid-string>"}
/// For the initial port, we store CIDs as raw strings.
pub fn deserialize_dag_cid<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: Deserializer<'de>,
{
    let value = Value::deserialize(deserializer)?;

    // Check if it's a dag-json CID link
    if let Value::Object(map) = &value
        && let Some(Value::String(cid_str)) = map.get("/")
    {
        return Ok(cid_str.clone());
    }

    Err(serde::de::Error::custom("Expected dag-json CID link"))
}

