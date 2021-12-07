#![no_main]
use libfuzzer_sys::fuzz_target;
use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

use atm_parser_helper::ParserHelper;

use atm_parser_helper_common_syntax::{
    *,
    testing::*,
};

fuzz_target!(|data: &[u8]| {
    match <Utf8String>::arbitrary(&mut Unstructured::new(data)) {
        Ok(s) => {
            let mut enc = Vec::new();
            s.encode(&mut enc);
            let mut p = ParserHelper::new(&enc);

            match parse_utf8_string::<Utf8StringError>(&mut p) {
                Err(e) => {
                    println!("{:?}", s);
                    println!("{:?}", std::str::from_utf8(&enc[..]).unwrap());
                    println!("{:?}", enc);
                    println!("{:?}", e);
                    panic!("Should have successfully parsed the input into a byte string.");
                }
                Ok(dec) => if dec != s.to_value() {
                    println!("{:?}", s);
                    println!("{:?}", std::str::from_utf8(&enc[..]).unwrap());
                    println!("{:?}", enc);
                    println!("decoded: {:?}", dec);
                    panic!("Should have successfully parsed the input into a byte string.");
                }
            }
        }
        _ => {}
    }
});
