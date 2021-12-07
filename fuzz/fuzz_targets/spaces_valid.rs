#![no_main]
use libfuzzer_sys::fuzz_target;
use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

use atm_parser_helper::ParserHelper;

use atm_parser_helper_common_syntax::{
    spaces,
    testing::{
        Spaces, SpacesError,
    },
};

fuzz_target!(|data: &[u8]| {
    match <Spaces>::arbitrary(&mut Unstructured::new(data)) {
        Ok(s) => {
            let mut enc = Vec::new();
            s.encode(&mut enc);
            let mut p = ParserHelper::new(&enc);

            assert!(spaces::<SpacesError>(&mut p).is_ok());
        }
        _ => {}
    }
});
