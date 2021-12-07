#![no_main]
use libfuzzer_sys::fuzz_target;
use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

use std::str::FromStr;

use atm_parser_helper::ParserHelper;

use atm_parser_helper_common_syntax::{
    *,
    testing::*,
};

fuzz_target!(|data: &[u8]| {
    match <TestNumber>::arbitrary(&mut Unstructured::new(data)) {
        Ok(s) => {
            let mut enc = Vec::new();
            s.encode(&mut enc);
            let mut p = ParserHelper::new(&enc);

            match parse_number::<i64, f64, NumberError>(&mut p, number_i64_from_decimal, number_i64_from_hex, number_i64_from_binary, number_f64_from_s, f64::NEG_INFINITY, f64::INFINITY, f64::NAN) {
                Err(e) => {
                    println!("{:?}", s);
                    println!("{:?}", std::str::from_utf8(&enc[..]).unwrap());
                    println!("{:?}", e);
                    panic!("Should have successfully parsed the input into a f64.")
                }
                Ok(dec) => {
                    if let Number::Float(f) = s.to_value() {
                        if f.is_nan() {
                            match dec {
                                Number::Float(dec_f) => assert!(dec_f.is_nan()),
                                Number::Integer(_) => panic!(),
                            }
                            return;
                        }
                    }

                    assert_eq!(dec, s.to_value());
                }
            }
        }
        _ => {}
    }
});

fn number_f64_from_s(s: &str) -> Result<f64, NumberError> {
    f64::from_str(s).map_err(|_| panic!())
}
