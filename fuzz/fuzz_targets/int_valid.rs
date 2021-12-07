#![no_main]
use libfuzzer_sys::fuzz_target;
use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

use atm_parser_helper::ParserHelper;

use atm_parser_helper_common_syntax::{
    *,
    testing::*,
};

fuzz_target!(|data: &[u8]| {
    match <Int>::arbitrary(&mut Unstructured::new(data)) {
        Ok(s) => {
            let mut enc = Vec::new();
            s.encode(&mut enc);
            let mut p = ParserHelper::new(&enc);

            assert_eq!(parse_int::<i64, IntError>(&mut p, i64_from_decimal, i64_from_hex, i64_from_binary).unwrap(), s.to_value());
        }
        _ => {}
    }
});
