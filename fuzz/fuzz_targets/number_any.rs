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
    let _ = parse_number::<i64, f64, NumberError>(&mut p, number_i64_from_decimal, number_i64_from_hex, number_i64_from_binary, number_f64_from_s, f64::NEG_INFINITY, f64::INFINITY, f64::NAN);
});

fn number_f64_from_s(s: &str) -> Result<f64, NumberError> {
    f64::from_str(s).map_err(|_| panic!())
}
