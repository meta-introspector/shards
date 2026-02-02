use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
pub struct SimpleExprMonster {
    pub expr: String,
    pub fold: u8,
    pub prime: u64,
    pub brainfuck: String,
}

pub fn compile_simpleexpr(json_path: &str) -> Result<Vec<SimpleExprMonster>, Box<dyn std::error::Error>> {
    let data = std::fs::read_to_string(json_path)?;
    let lean_expr: serde_json::Value = serde_json::from_str(&data)?;
    
    let mapping = HashMap::from([
        ("bvar", ("BVAR", 1, 71, "+><")),
        ("sort", ("SORT", 0, 2, "++[>+<]")),
        ("const", ("CONST", 2, 47, "[>+<]")),
        ("app", ("APP", 3, 19, ">>+")),
        ("lam", ("LAM", 4, 17, "+++[>]")),
        ("forallE", ("FORALL", 5, 13, "++++[>>]")),
    ]);
    
    let mut result = Vec::new();
    
    if let Some(rules) = lean_expr.pointer("/cnstInf/Rules") {
        if let Some(arr) = rules.as_array() {
            for rule in arr {
                if let Some(name) = rule["name"].as_str() {
                    let key = name.split('.').last().unwrap_or("");
                    if let Some(&(expr, fold, prime, bf)) = mapping.get(key) {
                        result.push(SimpleExprMonster {
                            expr: expr.to_string(),
                            fold,
                            prime,
                            brainfuck: bf.to_string(),
                        });
                    }
                }
            }
        }
    }
    
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_compile() {
        let path = "/mnt/data1/nix/time/2025/08/07/ragit/vendor/meta-introspector/solfunmeme-dioxus/hg_datasets/microlean4/SimpleExpr.rec_686e510a6699f2e1ff1b216c16d94cd379ebeca00c030a79a3134adff699e06c.json";
        let result = compile_simpleexpr(path).unwrap();
        assert_eq!(result.len(), 6);
        assert_eq!(result[0].prime, 71); // bvar → cusp
    }
}
