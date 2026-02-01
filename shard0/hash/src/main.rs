use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::fs::{self, File};
use std::io::{BufRead, BufReader};
use std::sync::Arc;
use parquet::file::properties::WriterProperties;
use parquet::file::writer::SerializedFileWriter;
use parquet::schema::parser::parse_message_type;
use arrow::array::{StringArray, UInt8Array, UInt64Array, Int64Array};
use arrow::record_batch::RecordBatch;
use arrow::datatypes::{Schema, Field, DataType};
use parquet::arrow::ArrowWriter;
use chrono::Utc;

fn hash_fn(s: &str, seed: u64) -> u64 {
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    s.hash(&mut hasher);
    hasher.finish()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let file = File::open("../../depth2")?;
    let reader = BufReader::new(file);
    
    let mut paths = Vec::new();
    let mut shards = Vec::new();
    let mut hash_sums = Vec::new();
    let mut proposal_ids = Vec::new();
    let mut timestamps = Vec::new();
    
    let mut proposal_id = 0u64;
    let now = Utc::now().timestamp();
    
    for line in reader.lines() {
        let path = line?;
        let mut sum: u64 = 0;
        
        for i in 0..71 {
            let h = hash_fn(&path, i);
            sum = sum.wrapping_add(h);
        }
        
        let shard = (sum % 71) as u8;
        
        paths.push(path);
        shards.push(shard);
        hash_sums.push(sum);
        proposal_ids.push(proposal_id);
        timestamps.push(now);
        
        proposal_id += 1;
    }
    
    let schema = Arc::new(Schema::new(vec![
        Field::new("entry_path", DataType::Utf8, false),
        Field::new("target_shard", DataType::UInt8, false),
        Field::new("hash_sum", DataType::UInt64, false),
        Field::new("proposal_id", DataType::UInt64, false),
        Field::new("timestamp", DataType::Int64, false),
    ]));
    
    let batch = RecordBatch::try_new(
        schema.clone(),
        vec![
            Arc::new(StringArray::from(paths)),
            Arc::new(UInt8Array::from(shards)),
            Arc::new(UInt64Array::from(hash_sums)),
            Arc::new(UInt64Array::from(proposal_ids)),
            Arc::new(Int64Array::from(timestamps)),
        ],
    )?;
    
    fs::create_dir_all("../data/parquet")?;
    let file = File::create("../data/parquet/proposals.parquet")?;
    let mut writer = ArrowWriter::try_new(file, schema, None)?;
    writer.write(&batch)?;
    writer.close()?;
    
    println!("Generated {} proposals", proposal_id);
    
    Ok(())
}
