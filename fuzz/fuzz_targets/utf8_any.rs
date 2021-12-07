#![no_main]
use libfuzzer_sys::fuzz_target;

use atm_parser_helper::ParserHelper;

use atm_parser_helper_common_syntax::{
    *,
    testing::*,
};

fuzz_target!(|data: &[u8]| {
    let mut p = ParserHelper::new(data);
    let _ = parse_utf8_string::<Utf8StringError>(&mut p);
});
