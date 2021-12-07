use std::collections::{BTreeMap, BTreeSet};

use arbitrary::{Arbitrary, Unstructured};
use pretty_dtoa::{dtoa, FmtFloatConfig};
use atm_parser_helper::Eoi;

use crate::{Number, WhiteSpaceE, IntLiteralE, FloatLiteralE, ByteStringLiteralE, Utf8StringLiteralE};

#[derive(Arbitrary, Debug)]
pub struct Spaces(Vec<Space>);

impl Spaces {
    pub fn encode(&self, out: &mut Vec<u8>) {
        for s in &self.0 {
            s.0.encode(out);
        }
    }
}

#[derive(Debug)]
pub enum SpacesError {
    Eoi,
    Utf8Comment,
}

impl Eoi for SpacesError {
    fn eoi() -> Self {
        Self::Eoi
    }
}

impl WhiteSpaceE for SpacesError {
    fn utf8_comment() -> Self {
        Self::Utf8Comment
    }
}

#[derive(Debug)]
pub struct Space(Space_);

impl<'a> Arbitrary<'a> for Space {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        match Space_::arbitrary(u)? {
            Space_::Tab => Ok(Space(Space_::Tab)),
            Space_::LF => Ok(Space(Space_::LF)),
            Space_::CR => Ok(Space(Space_::CR)),
            Space_::Space => Ok(Space(Space_::Space)),
            Space_::Comment(c) => {
                if c.contains("\n") {
                    Err(arbitrary::Error::IncorrectFormat)
                } else {
                    Ok(Space(Space_::Comment(c)))
                }
            }
        }
    }
}

#[derive(Arbitrary, Debug)]
pub enum Space_ {
    Tab,
    LF,
    CR,
    Space,
    /// Must not contain a newline character (0x0a).
    Comment(String),
}

impl Space_ {
    pub fn encode(&self, out: &mut Vec<u8>) {
        match self {
            Space_::Tab => out.push(0x09),
            Space_::LF => out.push(0x0a),
            Space_::CR => out.push(0x0d),
            Space_::Space => out.push(0x20),
            Space_::Comment(c) => {
                out.push('#' as u8);
                out.extend_from_slice(c.as_bytes());
                out.push(0x0a);
            }
        }
    }
}

#[derive(Debug)]
pub enum IntError {
    Eoi,
    NoDigits,
    NotInt,
    OutOfBounds,
}

impl Eoi for IntError {
    fn eoi() -> Self {
        Self::Eoi
    }
}

impl IntLiteralE for IntError {
    fn int_no_digits() -> Self {
        Self::NoDigits
    }

    fn not_int_literal() -> Self {
        Self::NotInt
    }
}

pub fn i64_from_decimal(s: &str) -> Result<i64, IntError> {
    i64::from_str_radix(s, 10).map_err(|_| IntError::OutOfBounds)
}

pub fn i64_from_hex(s: &str) -> Result<i64, IntError> {
    i64::from_str_radix(s, 16).map_err(|_| IntError::OutOfBounds)
}

pub fn i64_from_binary(s: &str) -> Result<i64, IntError> {
    i64::from_str_radix(s, 2).map_err(|_| IntError::OutOfBounds)
}

#[derive(Arbitrary, Debug)]
pub enum Base {
    Binary,
    Hex(BTreeSet<usize> /* capitalize */),
    Decimal,
}

#[derive(Arbitrary, Debug)]
pub struct Int {
    n: i64,
    explicit_sign: bool,
    base: Base,
    underscores: BTreeMap<usize, u8>, // keys are positions in the number encoding, values the number of inserted underscores
    leading_zeros: u8,
}

impl Int {
    pub fn to_value(&self) -> i64 {
        self.n
    }

    pub fn encode(&self, out: &mut Vec<u8>) {
        let mut tmp = Vec::new();

        if self.n < 0 {
            out.push('-' as u8);
        } else if self.explicit_sign {
            if let Base::Decimal = self.base {
                out.push('+' as u8);
            }
        }

        if self.n >= 0 {
            match self.base {
                Base::Binary => {
                    out.extend_from_slice(b"0b");
                }
                Base::Hex(_) => {
                    out.extend_from_slice(b"0x");
                }
                Base::Decimal => {}
            }
        }

        for _ in 0..(self.leading_zeros as usize) {
            tmp.push('0' as u8);
        }

        if self.n >= 0 {
            match &self.base {
                Base::Binary => {
                    tmp.extend_from_slice(&format!("{:#b}", self.n).as_bytes()[2..]);
                }
                Base::Hex(capitalized) => {
                    tmp.extend_from_slice(&format!("{:#x}", self.n).as_bytes()[2..]);
                    let mut tmp2 = Vec::new();
                    for (i, c) in tmp.iter().enumerate() {
                        if capitalized.contains(&i) {
                            tmp2.push(char::from_u32(*c as u32).unwrap().to_ascii_uppercase() as u8);
                        } else {
                            tmp2.push(*c);
                        }
                    }
                    tmp = tmp2;
                }
                Base::Decimal => {
                    tmp.extend_from_slice(format!("{}", self.n).as_bytes());
                }
            }
        } else {
            if self.n == i64::MIN {
                tmp.extend_from_slice(format!("{}", 9223372036854775808u64).as_bytes());
            } else {
                tmp.extend_from_slice(format!("{}", self.n.abs()).as_bytes());
            }
        }

        for (i, b) in tmp.iter().enumerate() {
            out.push(*b);
            if let Some(m) = self.underscores.get(&i) {
                for _ in 0..((*m) as usize) {
                    out.push('_' as u8);
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum FloatError {
    Eoi,
    LeadingDigits,
    NoPoint,
    TrailingDigits,
    ExponentDigits,
    NotFloat,
}

impl Eoi for FloatError {
    fn eoi() -> Self {
        Self::Eoi
    }
}

impl FloatLiteralE for FloatError {
    fn float_no_leading_digits() -> Self {
        Self::LeadingDigits
    }

    fn float_no_point() -> Self {
        Self::NoPoint
    }

    fn float_no_trailing_digits() -> Self {
        Self::TrailingDigits
    }

    fn float_no_exponent_digits() -> Self {
        Self::ExponentDigits
    }

    fn not_float_literal() -> Self {
        Self::NotFloat
    }
}

#[derive(Arbitrary, Debug)]
pub struct Float {
    n: f64,
    explicit_sign: bool,
    underscores: BTreeMap<usize, u8>, // keys are positions in the number encoding, values the number of inserted underscores
    min_sig_digits: u8,
    min_decimal_digits: i8,
    e_break: i8,
    which_e_break: bool,
    capitalize_e: bool,
}

impl Float {
    pub fn to_value(&self) -> f64 {
        self.n
    }

    pub fn encode(&self, out: &mut Vec<u8>) {
        if self.n.is_nan() {
            out.extend_from_slice(b"NaN");
        } else if self.n == f64::INFINITY {
            out.extend_from_slice(b"Inf");
        } else if self.n == f64::NEG_INFINITY {
            out.extend_from_slice(b"-Inf");
        } else {
            let mut config = FmtFloatConfig::default()
                .add_point_zero(true)
                .min_significant_digits(self.min_sig_digits)
                .min_decimal_digits(self.min_decimal_digits)
                .capitalize_e(self.capitalize_e);

            if self.which_e_break {
                config.lower_e_break  = self.e_break;
            } else {
                config.upper_e_break = self.e_break;
            }

            let mut tmp = Vec::new();

            if self.n > 0.0 && self.explicit_sign {
                out.push('+' as u8);
            }

            tmp.extend_from_slice(dtoa(self.n, config).as_bytes());

            for (i, b) in tmp.iter().enumerate() {
                out.push(*b);
                if let Some(m) = self.underscores.get(&i) {
                    if b.is_ascii_digit() {
                        for _ in 0..((*m) as usize) {
                            out.push('_' as u8);
                        }
                    }
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum NumberError {
    Eoi,
    NoDigits,
    NotInt,
    OutOfBounds,
    LeadingDigits,
    NoPoint,
    TrailingDigits,
    ExponentDigits,
    NotFloat,
}

impl Eoi for NumberError {
    fn eoi() -> Self {
        Self::Eoi
    }
}

impl IntLiteralE for NumberError {
    fn int_no_digits() -> Self {
        Self::NoDigits
    }

    fn not_int_literal() -> Self {
        Self::NotInt
    }
}

impl FloatLiteralE for NumberError {
    fn float_no_leading_digits() -> Self {
        Self::LeadingDigits
    }

    fn float_no_point() -> Self {
        Self::NoPoint
    }

    fn float_no_trailing_digits() -> Self {
        Self::TrailingDigits
    }

    fn float_no_exponent_digits() -> Self {
        Self::ExponentDigits
    }

    fn not_float_literal() -> Self {
        Self::NotFloat
    }
}

#[derive(Arbitrary, Debug)]
pub enum TestNumber {
    Float(Float),
    Integer(Int),
}

impl TestNumber {
    pub fn to_value(&self) -> Number<i64, f64> {
        match self {
            TestNumber::Float(n) => Number::Float(n.to_value()),
            TestNumber::Integer(n) => Number::Integer(n.to_value()),
        }
    }

    pub fn encode(&self, out: &mut Vec<u8>) {
        match self {
            TestNumber::Float(n) => n.encode(out),
            TestNumber::Integer(n) => n.encode(out),
        }
    }
}

pub fn number_i64_from_decimal(s: &str) -> Result<i64, NumberError> {
    i64::from_str_radix(s, 10).map_err(|_| NumberError::OutOfBounds)
}

pub fn number_i64_from_hex(s: &str) -> Result<i64, NumberError> {
    i64::from_str_radix(s, 16).map_err(|_| NumberError::OutOfBounds)
}

pub fn number_i64_from_binary(s: &str) -> Result<i64, NumberError> {
    i64::from_str_radix(s, 2).map_err(|_| NumberError::OutOfBounds)
}

#[derive(Debug)]
pub enum ByteStringError {
    Eoi,
    OddHex,
    NumberBinary,
    NotByteString,
    Comma,
    OutOfBounds,
    Space(SpacesError),
    Int(IntError),
}

impl Eoi for ByteStringError {
    fn eoi() -> Self {
        Self::Eoi
    }
}

impl WhiteSpaceE for ByteStringError {
    fn utf8_comment() -> Self {
        Self::Space(SpacesError::utf8_comment())
    }
}

impl IntLiteralE for ByteStringError {
    fn int_no_digits() -> Self {
        Self::Int(IntError::int_no_digits())
    }

    fn not_int_literal() -> Self {
        Self::Int(IntError::not_int_literal())
    }
}

impl ByteStringLiteralE for ByteStringError {
    fn odd_hex_digits() -> Self {
        Self::OddHex
    }

    fn number_binary_digits() -> Self {
        Self::NumberBinary
    }

    fn expected_comma() -> Self {
        Self::Comma
    }

    fn byte_out_of_bounds() -> Self {
        Self::OutOfBounds
    }

    fn not_byte_string_literal() -> Self {
        Self::NotByteString
    }
}

#[derive(Arbitrary, Debug)]
pub enum ByteString {
    Hex {
        bytes: Vec<u8>,
        capitalized: BTreeSet<usize>,
        underscores: BTreeMap<usize, u8>,
    },
    Binary {
        bytes: Vec<u8>,
        underscores: BTreeMap<usize, u8>,
    },
    Integer {
        bytes: Vec<(Spaces, Int, Spaces)>,
        trailing_comma: Option<Spaces>,
    }
}

impl ByteString {
    pub fn to_value(&self) -> Vec<u8> {
        match self {
            ByteString::Hex { bytes, .. } => bytes.clone(),
            ByteString::Binary { bytes, .. } => bytes.clone(),
            ByteString::Integer { bytes, .. } => bytes.iter().map(|(_, b, _)| {
                let n = b.to_value();
                if n >= 0 && n <= 255 {
                    n as u8
                } else {
                    0
                }
            }).collect(),
        }
    }

    pub fn encode(&self, out: &mut Vec<u8>) {
        match self {
            ByteString::Hex { bytes, capitalized, underscores } => {
                out.extend_from_slice(b"@x");
                let mut tmp = Vec::new();

                for (i, b) in bytes.iter().enumerate() {
                    tmp.push(as_hex_digit(b >> 4, capitalized.contains(&(2 * i))));
                    tmp.push(as_hex_digit(b & 0x0f, capitalized.contains(&(2 * i + 1))));
                }

                for (i, b) in tmp.iter().enumerate() {
                    out.push(*b);
                    if let Some(m) = underscores.get(&i) {
                        for _ in 0..((*m) as usize) {
                            out.push('_' as u8);
                        }
                    }
                }
            }
            ByteString::Binary { bytes, underscores } => {
                out.extend_from_slice(b"@b");
                let mut tmp = Vec::new();

                for b in bytes.iter() {
                    let mut byte = *b;
                    for _ in 0..8 {
                        tmp.push(if (byte & 0b1000_0000) == 0 { '0' as u8 } else { '1' as u8 });
                        byte = byte << 1;
                    }
                }

                for (i, b) in tmp.iter().enumerate() {
                    out.push(*b);
                    if let Some(m) = underscores.get(&i) {
                        for _ in 0..((*m) as usize) {
                            out.push('_' as u8);
                        }
                    }
                }
            }
            ByteString::Integer { bytes, trailing_comma } => {
                out.extend_from_slice(b"@[");
                let len = bytes.len();
                for (i, (s1, b, s2)) in bytes.iter().enumerate() {
                    s1.encode(out);

                    let n = b.to_value();
                    if n >= 0 && n <= 255 {
                        b.encode(out);
                    } else {
                        out.push('0' as u8);
                    }

                    s2.encode(out);

                    if i + 1 == len {
                        match trailing_comma {
                            None => break,
                            Some(s) => {
                                out.push(',' as u8);
                                s.encode(out);
                            }
                        }
                    } else {
                        out.push(',' as u8);
                    }
                }
                out.push(']' as u8);
            }
        }
    }
}

fn as_hex_digit(nibble: u8, capitalize: bool) -> u8 {
    if nibble <= 9 {
        return 0x30 + nibble;
    } else if nibble <= 15 {
        return 0x41 + nibble + if capitalize { 0 } else { 32 } - 10;
    } else {
        panic!("not a nibble")
    }
}

#[derive(Debug, Arbitrary)]
pub enum Scalar {
    Regular(char),
    LF,
    Tab,
    Null,
    Decimal(char),
}

impl Scalar {
    fn to_value(&self) -> char {
        match self {
            Scalar::Regular(c) | Scalar::Decimal(c) => *c,
            Scalar::LF => '\n',
            Scalar::Tab => '\t',
            Scalar::Null => '\0',
        }
    }

    fn encode(&self, out: &mut Vec<u8>) {
        match self {
            Scalar::Regular('\\') => out.extend_from_slice(b"\\\\"),
            Scalar::Regular('"') => out.extend_from_slice(b"\\\""),
            Scalar::Regular(c) => out.extend_from_slice(c.to_string().as_bytes()),
            Scalar::LF => out.extend_from_slice(b"\\n"),
            Scalar::Tab => out.extend_from_slice(b"\\t"),
            Scalar::Null => out.extend_from_slice(b"\\0"),
            Scalar::Decimal(c) => {
                for b in c.escape_unicode() {
                    if b != 'u' {
                        out.push(b as u8);
                    }
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct RawString(u8, String);

impl<'a> Arbitrary<'a> for RawString {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let (ats, s) = <(u8, String)>::arbitrary(u)?;
        if ats == 0 {
            return Err(arbitrary::Error::IncorrectFormat);
        }

        let mut consecutive_ats = None;
        for b in s.as_bytes() {
            match b {
                0x22 => consecutive_ats = Some(0),
                0x40 => {
                    match consecutive_ats.as_mut() {
                        None => {}
                        Some(n) => {
                            *n += 1;
                            if *n >= ats {
                                return Err(arbitrary::Error::IncorrectFormat);
                            }
                        }
                    }
                }
                _ => consecutive_ats = None,
            }
        }

        return Ok(RawString(ats, s));
    }
}

#[derive(Debug, Arbitrary)]
pub enum Utf8String {
    Escaping(Vec<Scalar>),
    Raw(RawString),
}

impl Utf8String {
    pub fn to_value(&self) -> String {
        match self {
            Utf8String::Escaping(scalars) => scalars.iter().map(|c| c.to_value()).collect(),
            Utf8String::Raw(RawString(_, s)) => s.clone(),
        }
    }

    pub fn encode(&self, out: &mut Vec<u8>) {
        match self {
            Utf8String::Escaping(scalars) => {
                out.push('"' as u8);
                for c in scalars {
                    c.encode(out);
                }
                out.push('"' as u8);
            }
            Utf8String::Raw(RawString(ats, s)) => {
                for _ in 0..*ats {
                    out.push('@' as u8);
                }
                out.push('"' as u8);
                out.extend_from_slice(s.as_bytes());
                out.push('"' as u8);
                for _ in 0..*ats {
                    out.push('@' as u8);
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum Utf8StringError {
    Eoi,
    RawNotUtf8,
    RawToManyAts,
    EscapingNotUtf8,
    InvalidEscapeSequence,
    UnicodeEscapeNumberDigits,
    UnicodeEscapeInvalidScalar,
    UnicodeEscapeNoClosing,
    NotUtf8Literal,
}

impl Eoi for Utf8StringError {
    fn eoi() -> Self {
        Self::Eoi
    }
}

impl Utf8StringLiteralE for Utf8StringError {
    fn raw_not_utf8() -> Self {
        Utf8StringError::RawNotUtf8
    }

    fn raw_too_many_ats() -> Self {
        Utf8StringError::RawToManyAts
    }

    fn escaping_not_utf8() -> Self {
        Utf8StringError::EscapingNotUtf8
    }

    fn invalid_escape_sequence() -> Self {
        Utf8StringError::InvalidEscapeSequence
    }

    fn unicode_escape_number_digits() -> Self {
        Utf8StringError::UnicodeEscapeNumberDigits
    }

    fn unicode_escape_invalid_scalar() -> Self {
        Utf8StringError::UnicodeEscapeInvalidScalar
    }

    fn unicode_escape_no_closing() -> Self {
        Utf8StringError::UnicodeEscapeNoClosing
    }

    fn not_utf8_string_literal() -> Self {
        Utf8StringError::NotUtf8Literal
    }
}
