use std::collections::BTreeMap;

use frame_metadata::RuntimeMetadataV14;

use super::ClientT;

pub struct ClientDump {
    pub meta: RuntimeMetadataV14,
    pub data: BTreeMap<Vec<u8>, Vec<u8>>,
}

fn next(key: &mut [u8]) {
    for i in (0..key.len()).rev() {
        let (v, overflown) = key[i].overflowing_add(1);
        key[i] = v;
        if !overflown {
            break;
        }
    }
}

impl ClientT for ClientDump {
    fn get_keys(&self, prefix: &[u8]) -> super::Result<Vec<Vec<u8>>> {
        let mut last = prefix.to_vec();
        next(&mut last);
        Ok(self
            .data
            .range(prefix.to_vec()..last)
            .map(|(k, _)| k.clone())
            .collect())
    }

    fn get_storage(&self, key: &[u8]) -> super::Result<Option<Vec<u8>>> {
        Ok(self.data.get(key).cloned())
    }

    fn preload_storage(&self, _keys: &[&Vec<u8>]) -> super::Result<()> {
        Ok(())
    }

    fn contains_data_for(&self, prefix: &[u8]) -> super::Result<bool> {
        Ok(self
            .data
            .range(prefix.to_vec()..)
            .next()
            .map(|(k, _)| k.starts_with(prefix))
            .unwrap_or(false))
    }

    fn get_metadata(&self) -> super::Result<RuntimeMetadataV14> {
        Ok(self.meta.clone())
    }
}
