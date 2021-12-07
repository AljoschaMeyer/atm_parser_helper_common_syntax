#![no_main]
use libfuzzer_sys::fuzz_target;

use atm_parser_helper::ParserHelper;

use atm_parser_helper_common_syntax::{
    *,
    testing::*,
};

fuzz_target!(|data: &[u8]| {
    let mut p = ParserHelper::new(data);
    let _ = parse_int::<i64, IntError>(&mut p, i64_from_decimal, i64_from_hex, i64_from_binary);
});
