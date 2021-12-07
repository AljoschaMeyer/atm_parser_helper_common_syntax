#![no_main]
use libfuzzer_sys::fuzz_target;

use std::str::FromStr;

use atm_parser_helper::ParserHelper;

use atm_parser_helper_common_syntax::{
    *,
    testing::*,
};

fuzz_target!(|data: &[u8]| {
    let mut p = ParserHelper::new(data);
    let _ = parse_float::<f64, FloatError>(&mut p, f64_from_s, f64::NEG_INFINITY, f64::INFINITY, f64::NAN);
});

fn f64_from_s(s: &str) -> Result<f64, FloatError> {
    f64::from_str(s).map_err(|_| panic!())
}
