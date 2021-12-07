use atm_parser_helper::{Eoi, Error, ParserHelper};

#[cfg(feature = "arbitrary")]
pub mod testing;

/// A trait for error types that can represent errors occurring when parsing whitespace.
pub trait WhiteSpaceE : Eoi {
    /// Create a value indicating that a comment contains non-UTF-8 content.
    fn utf8_comment() -> Self;
}

/// Parse an arbitrary amount of whitespace.
pub fn spaces<E: WhiteSpaceE>(p: &mut ParserHelper) -> Result<(), Error<E>> {
    loop {
        match p.peek_or_end() {
            Some(0x09) | Some(0x0a) | Some(0x0d) | Some(0x20) => p.advance(1),
            Some(0x23) => comment(p)?,
            Some(_) | None => return Ok(()),
        }
    }
}

fn comment<E: WhiteSpaceE>(p: &mut ParserHelper) -> Result<(), Error<E>> {
    let start = p.position();
    p.advance(1); // #
    loop {
        match p.next_or_end() {
            Some(0x0a) | None => {
                match std::str::from_utf8(p.slice(start..p.position())) {
                    Ok(_) => return Ok(()),
                    Err(_) => return p.fail_at_position(E::utf8_comment(), start),
                }
            }
            Some(_) => {}
        }
    }
}

/// A trait for error types that can represent errors occurring when parsing an integer literal.
pub trait IntLiteralE : Eoi {
    /// Create a value indicating that an integer literal contains no digits.
    fn int_no_digits() -> Self;
    /// Create a value indicating that the input does not contain (even the beginning of) an integer literal.
    fn not_int_literal() -> Self;
}

/// Parse an integer literal.
pub fn parse_int<I, E: IntLiteralE>(
    p: &mut ParserHelper,
    from_decimal: fn(&str) -> Result<I, E>,
    from_hex: fn(&str) -> Result<I, E>,
    from_binary: fn(&str) -> Result<I, E>,
) -> Result<I, Error<E>> {
    let start = p.position();

    let negative = p.advance_over(b"-");
    let has_sign = negative || p.advance_over(b"+");

    let is_hex = !has_sign && p.advance_over(b"0x");
    let is_binary = !is_hex && (!has_sign && p.advance_over(b"0b"));

    if is_hex {
        if !is_hex_digit(p.peek()?) {
            return p.fail(E::int_no_digits());
        }

        let start = p.position();
        p.skip(is_hex_digit_or_underscore);

        let digits_with_underscores = unsafe { std::str::from_utf8_unchecked(p.slice(start..p.position())) };
        let without_underscores = digits_with_underscores.replace("_", "");
        match from_hex(&without_underscores) {
            Ok(n) => return Ok(n),
            Err(e) => return p.fail(e),
        }
    } else if is_binary {
        if !is_binary_digit(p.peek()?) {
            return p.fail(E::int_no_digits());
        }

        let start = p.position();
        p.skip(is_binary_digit_or_underscore);

        let digits_with_underscores = unsafe { std::str::from_utf8_unchecked(p.slice(start..p.position())) };
        let without_underscores = digits_with_underscores.replace("_", "");
        match from_binary(&without_underscores) {
            Ok(n) => return Ok(n),
            Err(e) => return p.fail(e),
        }
    } else {
        if !is_digit(p.peek()?) {
            if has_sign {
                return p.fail(E::int_no_digits());
            } else {
                return p.fail(E::not_int_literal());
            }
        }

        p.skip(is_digit_or_underscore);

        let digits_with_underscores = unsafe { std::str::from_utf8_unchecked(p.slice(start..p.position())) };
        let without_underscores = digits_with_underscores.replace("_", "");
        match from_decimal(&without_underscores) {
            Ok(n) => return Ok(n),
            Err(e) => return p.fail(e),
        }
    }
}

/// A trait for error types that can represent errors occurring when parsing an integer literal.
pub trait FloatLiteralE : Eoi {
    /// Create a value indicating that a float literal contains no digits before the point.
    fn float_no_leading_digits() -> Self;
    /// Create a value indicating that a float literal contains no point.
    fn float_no_point() -> Self;
    /// Create a value indicating that a float literal contains no digits after the point.
    fn float_no_trailing_digits() -> Self;
    /// Create a value indicating that a float literal contains no digits as the exponent.
    fn float_no_exponent_digits() -> Self;
    /// Create a value indicating that the input does not contain (even the beginning of) a float literal.
    fn not_float_literal() -> Self;
}

/// Parse a floating-point number literal.
pub fn parse_float<F, E: FloatLiteralE>(
    p: &mut ParserHelper,
    from_s: fn(&str) -> Result<F, E>,
    neg_inf: F,
    pos_inf: F,
    nan: F,
) -> Result<F, Error<E>> {
    let start = p.position();

    let negative = p.advance_over(b"-");
    let has_sign = negative || p.advance_over(b"+");

    match p.peek()? {
        0x49 => {
            p.expect_bytes(b"Inf", E::not_float_literal())?;
            return Ok(if negative { neg_inf } else { pos_inf });
        }
        0x4e => {
            p.expect_bytes(b"NaN", E::not_float_literal())?;
            return Ok(nan);
        }
        _ => {}
    }

    if !is_digit(p.peek()?) {
        if has_sign {
            return p.fail(E::float_no_leading_digits());
        } else {
            return p.fail(E::not_float_literal());
        }
    }
    p.skip(is_digit_or_underscore);

    p.expect('.' as u8, E::float_no_point())?;

    if !is_digit(p.peek()?) {
        return p.fail(E::float_no_trailing_digits());
    }
    p.skip(is_digit_or_underscore);

    if let Ok(0x45 | 0x65) = p.peek::<E>() {
        p.advance(1);
        let negative = p.advance_over(b"-");
        if !negative {
            p.advance_over(b"+");
        }

        if !is_digit(p.peek()?) {
            return p.fail(E::float_no_exponent_digits());
        }
        p.skip(is_digit_or_underscore);
    }

    let digits_with_underscores = unsafe { std::str::from_utf8_unchecked(p.slice(start..p.position())) };
    let without_underscores = digits_with_underscores.replace("_", "");
    match from_s(&without_underscores) {
        Ok(n) => return Ok(n),
        Err(_) => panic!("Prior parsing should have ensured a valid input to f64::from_str"),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum Number<I, F> {
    Float(F),
    Integer(I),
}

/// Parse number literal.
pub fn parse_number<I, F, E: FloatLiteralE + IntLiteralE>(
    p: &mut ParserHelper,
    from_decimal: fn(&str) -> Result<I, E>,
    from_hex: fn(&str) -> Result<I, E>,
    from_binary: fn(&str) -> Result<I, E>,
    from_s: fn(&str) -> Result<F, E>,
    neg_inf: F,
    pos_inf: F,
    nan: F,
) -> Result<Number<I, F>, Error<E>> {
    let start = p.position();

    let negative = p.advance_over(b"-");
    let has_sign = negative || p.advance_over(b"+");

    match p.peek()? {
        0x49 => {
            p.expect_bytes(b"Inf", E::not_float_literal())?;
            return Ok(if negative { Number::Float(neg_inf) } else { Number::Float(pos_inf) });
        }
        0x4e => {
            p.expect_bytes(b"NaN", E::not_float_literal())?;
            return Ok(Number::Float(nan));
        }
        _ => {}
    }

    let is_hex = !has_sign && p.advance_over(b"0x");
    let is_binary = !is_hex && (!has_sign && p.advance_over(b"0b"));

    if is_hex {
        if !is_hex_digit(p.peek()?) {
            return p.fail(E::int_no_digits());
        }

        let start = p.position();
        p.skip(is_hex_digit_or_underscore);

        let digits_with_underscores = unsafe { std::str::from_utf8_unchecked(p.slice(start..p.position())) };
        let without_underscores = digits_with_underscores.replace("_", "");
        match from_hex(&without_underscores) {
            Ok(n) => return Ok(Number::Integer(n)),
            Err(e) => return p.fail(e),
        }
    } else if is_binary {
        if !is_binary_digit(p.peek()?) {
            return p.fail(E::int_no_digits());
        }

        let start = p.position();
        p.skip(is_binary_digit_or_underscore);

        let digits_with_underscores = unsafe { std::str::from_utf8_unchecked(p.slice(start..p.position())) };
        let without_underscores = digits_with_underscores.replace("_", "");
        match from_binary(&without_underscores) {
            Ok(n) => return Ok(Number::Integer(n)),
            Err(e) => return p.fail(e),
        }
    } else {
        if !is_digit(p.peek()?) {
            if has_sign {
                return p.fail(E::int_no_digits());
            } else {
                return p.fail(E::not_int_literal());
            }
        }

        p.skip(is_digit_or_underscore);

        match p.peek::<E>() {
            Ok(0x2e) => {
                p.advance(1);
                if !is_digit(p.peek()?) {
                    return p.fail(E::float_no_trailing_digits());
                }
                p.skip(is_digit_or_underscore);

                if let Ok(0x45 | 0x65) = p.peek::<E>() {
                    p.advance(1);
                    let negative = p.advance_over(b"-");
                    if !negative {
                        p.advance_over(b"+");
                    }

                    if !is_digit(p.peek()?) {
                        return p.fail(E::float_no_exponent_digits());
                    }
                    p.skip(is_digit_or_underscore);
                }

                let digits_with_underscores = unsafe { std::str::from_utf8_unchecked(p.slice(start..p.position())) };
                let without_underscores = digits_with_underscores.replace("_", "");
                match from_s(&without_underscores) {
                    Ok(n) => return Ok(Number::Float(n)),
                    Err(_) => panic!("Prior parsing should have ensured a valid input to f64::from_str"),
                }
            }

            _ => {
                let digits_with_underscores = unsafe { std::str::from_utf8_unchecked(p.slice(start..p.position())) };
                let without_underscores = digits_with_underscores.replace("_", "");
                match from_decimal(&without_underscores) {
                    Ok(n) => return Ok(Number::Integer(n)),
                    Err(e) => return p.fail(e),
                }
            }
        }
    }
}

/// A trait for error types that can represent errors occurring when parsing a byte string literal.
pub trait ByteStringLiteralE : Eoi + WhiteSpaceE + IntLiteralE {
    /// Create a value indicating that a hexdecimal byte string literal contains an odd number of digits.
    fn odd_hex_digits() -> Self;
    /// Create a value indicating that a binary byte string literal contains a number of digits not divisible by eight.
    fn number_binary_digits() -> Self;
    /// Create a value indicating that the next input byte should be a ','.
    fn expected_comma() -> Self;
    /// Create a value indicating that a integer byte string literal contains a number that is not a u8.
    fn byte_out_of_bounds() -> Self;
    /// Create a value indicating that the input does not contain (even the beginning of) a byte string literal.
    fn not_byte_string_literal() -> Self;
}

/// Parse a byte string literal.
pub fn parse_byte_string<E: ByteStringLiteralE>(p: &mut ParserHelper) -> Result<Vec<u8>, Error<E>> {
    p.expect('@' as u8, E::not_byte_string_literal())?;
    match p.next()? {
        0x5b => {
            let mut r = Vec::new();
            loop {
                spaces(p)?;
                if p.peek()? == (']' as u8) {
                    p.advance(1);
                    return Ok(r);
                }

                let b = parse_int(p, u8_from_decimal, u8_from_hex, u8_from_binary)?;
                r.push(b);

                spaces(p)?;

                if p.peek()? == (']' as u8) {
                    p.advance(1);
                    return Ok(r);
                } else if p.peek()? == (',' as u8) {
                    p.advance(1);
                } else {
                    return p.fail(E::expected_comma());
                }
            }
        }
        0x78 => {
            let start = p.position();
            p.skip(is_hex_digit_or_underscore);

            let digits_with_underscores = unsafe { std::str::from_utf8_unchecked(p.slice(start..p.position())) };
            let without_underscores = digits_with_underscores.replace("_", "");

            if without_underscores.len() % 2 == 0 {
                let mut buf = Vec::new();
                let mut i = 0;
                while i < without_underscores.len() {
                    buf.push(u8::from_str_radix(unsafe {std::str::from_utf8_unchecked(&without_underscores.as_bytes()[i..i + 2])}, 16).unwrap());
                    i += 2;
                }
                return Ok(buf);
            } else {
                p.fail(E::odd_hex_digits())
            }
        }
        0x62 => {
            let start = p.position();
            p.skip(is_binary_digit_or_underscore);

            let digits_with_underscores = unsafe { std::str::from_utf8_unchecked(p.slice(start..p.position())) };
            let without_underscores = digits_with_underscores.replace("_", "");

            if without_underscores.len() % 8 == 0 {
                let mut buf = Vec::new();
                let mut i = 0;
                while i < without_underscores.len() {
                    buf.push(u8::from_str_radix(unsafe {std::str::from_utf8_unchecked(&without_underscores.as_bytes()[i..i + 8])}, 2).unwrap());
                    i += 8;
                }
                return Ok(buf);
            } else {
                p.fail(E::number_binary_digits())
            }
        }
        _ => p.fail(E::not_byte_string_literal()),
    }
}

/// A trait for error types that can represent errors occurring when parsing a UTF-8 string literal.
pub trait Utf8StringLiteralE : Eoi {
    /// Create a value indicating that a raw UTF-8 string literal contains non-utf8 bytes.
    fn raw_not_utf8() -> Self;
    /// Create a value indicating that a raw UTF-8 string literal starts with more than 255 `@`.
    fn raw_too_many_ats() -> Self;
    /// Create a value indicating that an escaping UTF-8 string literal contains non-utf8 bytes.
    fn escaping_not_utf8() -> Self;
    /// Create a value indicating that an escaping UTF-8 string literal contains a `\` followed by an invalid character.
    fn invalid_escape_sequence() -> Self;
    /// Create a value indicating that a unicode escape sequence contains an invalid number of digits.
    fn unicode_escape_number_digits() -> Self;
    /// Create a value indicating that a unicode escape sequence encodes a number that is not a unicode scalar.
    fn unicode_escape_invalid_scalar() -> Self;
    /// Create a value indicating that a unicode escape sequence is not terminated by a `}`.
    fn unicode_escape_no_closing() -> Self;
    /// Create a value indicating that the input does not contain (even the beginning of) a UTF-8 string literal.
    fn not_utf8_string_literal() -> Self;
}

/// Parse a UTF-8 string literal.
pub fn parse_utf8_string<E: Utf8StringLiteralE>(p: &mut ParserHelper) -> Result<String, Error<E>> {
    let start_ats = p.position();
    p.skip(is_at);
    let ats = p.position() - start_ats;

    p.expect('"' as u8, E::not_utf8_string_literal())?;
    let start = p.position();

    if ats == 0 {
        let mut s = String::new();

        loop {
            if p.advance_over(b"\"") {
                return Ok(s);
            } else {
                s.push(parse_char(p)?);
            }
        }
    } else {
        let mut consecutive_ats = None;
        let mut end = 0;
        loop {
            let b = p.next()?;
            match b {
                0x22 => {
                    consecutive_ats = Some(0);
                    end = p.position() - 1;
                }
                0x40 => {
                    match consecutive_ats.as_mut() {
                        None => {}
                        Some(n) => {
                            *n += 1;
                            if *n > 255 {
                                return p.fail(E::raw_too_many_ats());
                            }
                            if *n == ats {
                                return std::str::from_utf8(p.slice(start..end))
                                    .map(|s| s.to_string())
                                    .map_err(|_| p.fail::<(), E>(E::raw_not_utf8()).unwrap_err());
                            }
                        }
                    }
                }
                _ => consecutive_ats = None,
            }
        }
    }
}

fn parse_char<E: Utf8StringLiteralE>(p: &mut ParserHelper) -> Result<char, Error<E>> {
    let start = p.position();
    let fst = p.next()?;
    let mut scalar;
    if (fst & 0b1000_0000) == 0b0000_0000 {
        scalar = fst as u32;
    } else if (fst & 0b1110_0000) == 0b1100_0000 {
        scalar = (fst & 0b0001_1111) as u32;
        scalar <<= 6;
        scalar = ((p.next()? & 0b0011_1111) as u32) | scalar;
    } else if (fst & 0b1111_0000) == 0b1110_0000 {
        scalar = (fst & 0b0000_1111) as u32;
        scalar <<= 6;
        scalar = ((p.next()? & 0b0011_1111) as u32) | scalar;
        scalar <<= 6;
        scalar = ((p.next()? & 0b0011_1111) as u32) | scalar;
    } else if (fst & 0b1111_1000) == 0b1111_0000 {
        scalar = (fst & 0b0000_0111) as u32;
        scalar <<= 6;
        scalar = ((p.next()? & 0b0011_1111) as u32) | scalar;
        scalar <<= 6;
        scalar = ((p.next()? & 0b0011_1111) as u32) | scalar;
        scalar <<= 6;
        scalar = ((p.next()? & 0b0011_1111) as u32) | scalar;
    } else {
        return p.fail(E::escaping_not_utf8())?;
    }

    if let Err(_) = std::str::from_utf8(p.slice(start..p.position())) {
        return p.fail(E::escaping_not_utf8()); // catch overlong encodings etc
    }

    match core::char::from_u32(scalar) {
        None => return p.fail(E::escaping_not_utf8()),
        Some(c) => {
            if c == '\\' {
                match p.next()? {
                    0x22 => return Ok('\"'),
                    0x30 => return Ok('\0'),
                    0x5c => return Ok('\\'),
                    0x6e => return Ok('\n'),
                    0x74 => return Ok('\t'),
                    0x7b => {
                        let start = p.position();
                        p.skip(is_hex_digit);
                        let end = p.position();
                        let len = end - start;

                        if len < 1 || len > 6 {
                            return p.fail(E::unicode_escape_number_digits());
                        }

                        let raw = p.slice(start..end);
                        let numeric = u32::from_str_radix(unsafe { std::str::from_utf8_unchecked(raw) }, 16).unwrap();

                        match std::char::from_u32(numeric) {
                            None => return p.fail(E::unicode_escape_invalid_scalar()),
                            Some(c) => {
                                p.expect('}' as u8, E::unicode_escape_no_closing())?;
                                return Ok(c);
                            }
                        }
                    }
                    _ => return p.fail(E::invalid_escape_sequence()),
                }
            } else {
                return Ok(c);
            }
        }
    }
}

fn is_at(b: u8) -> bool {
    b == ('@' as u8)
}

fn is_digit(byte: u8) -> bool {
    byte.is_ascii_digit()
}

fn is_hex_digit(byte: u8) -> bool {
    byte.is_ascii_hexdigit()
}

fn is_binary_digit(byte: u8) -> bool {
    byte == ('0' as u8) || byte == ('1' as u8)
}

fn is_digit_or_underscore(byte: u8) -> bool {
    byte == ('_' as u8) || byte.is_ascii_digit()
}

fn is_hex_digit_or_underscore(byte: u8) -> bool {
    byte == ('_' as u8) || is_hex_digit(byte)
}

fn is_binary_digit_or_underscore(byte: u8) -> bool {
    byte == ('_' as u8) || is_binary_digit(byte)
}

pub fn u8_from_decimal<E: ByteStringLiteralE>(s: &str) -> Result<u8, E> {
    u8::from_str_radix(s, 10).map_err(|_| E::byte_out_of_bounds())
}

pub fn u8_from_hex<E: ByteStringLiteralE>(s: &str) -> Result<u8, E> {
    u8::from_str_radix(s, 16).map_err(|_| E::byte_out_of_bounds())
}

pub fn u8_from_binary<E: ByteStringLiteralE>(s: &str) -> Result<u8, E> {
    u8::from_str_radix(s, 2).map_err(|_| E::byte_out_of_bounds())
}
