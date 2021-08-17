#![feature(generic_associated_types)]
#![doc = include_str!("../README.md")]

pub use autoproto_derive::{IsDefault, Message, Proto, ProtoEncode, ProtoScalar};

pub use prost;
pub use prost::bytes;

pub mod generic;
pub mod macros;

use prost::encoding::{DecodeContext, WireType};
use std::{
    borrow::Borrow,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    convert::{TryFrom, TryInto},
    fmt::{self, Debug},
    hash::Hash,
    marker::PhantomData,
    num::NonZeroU32,
};

pub trait Clear {
    fn clear(&mut self);
}

impl<T: Default> Clear for T {
    fn clear(&mut self) {
        *self = Default::default();
    }
}

pub trait ToProtoSpec {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result;
}

impl<T> IsDefault for PhantomData<T> {
    fn is_default(&self) -> bool {
        true
    }
}

impl<T> IsDefault for &'_ T
where
    T: IsDefault,
{
    fn is_default(&self) -> bool {
        (**self).is_default()
    }
}

// This is different to `()`, which is an empty struct (and so takes up space for the field tag + a
// marker for 0 bytes). `PhantomData` should not be encoded at all. In theory we shouldn't need to
// encode `()` either, but `prost` does and we're aiming for byte-for-byte compatibility.
impl<T> ProtoEncode for PhantomData<T> {
    fn encode_as_field(&self, _tag: NonZeroU32, _buf: &mut dyn bytes::BufMut) {}

    fn encoded_len_as_field(&self, _tag: NonZeroU32) -> usize {
        0
    }
}

impl<T> Proto for PhantomData<T> {
    fn merge_self(
        &mut self,
        wire_type: WireType,
        buf: &mut dyn bytes::Buf,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError> {
        <()>::merge_self(&mut (), wire_type, buf, ctx)
    }
}

pub trait ProtoEncode {
    /// Encode this type _as a field_. This is different to encoding it as a message (which is
    /// what `prost::Message:encode_raw` does), as base types such as integers are encoded
    /// differently as fields vs as messages.
    fn encode_as_field(&self, tag: NonZeroU32, buf: &mut dyn bytes::BufMut);

    /// Get the length if this type is encoded with its field tag.
    fn encoded_len_as_field(&self, tag: NonZeroU32) -> usize;
}

pub trait ProtoEncodeRepeated: ProtoEncode {
    fn encode_as_field_repeated<'a, I>(iter: I, tag: NonZeroU32, buf: &mut dyn bytes::BufMut)
    where
        I: ExactSizeIterator<Item = &'a Self> + Clone,
        Self: 'a;

    fn encoded_len_as_field_repeated<'a, I>(iter: I, tag: NonZeroU32) -> usize
    where
        I: ExactSizeIterator<Item = &'a Self>,
        Self: 'a;
}

impl<T> ProtoEncodeRepeated for T
where
    T: ProtoEncode + IsMessage,
{
    fn encode_as_field_repeated<'a, I>(iter: I, tag: NonZeroU32, buf: &mut dyn bytes::BufMut)
    where
        I: Iterator<Item = &'a Self> + Clone,
        Self: 'a,
    {
        for i in iter {
            i.encode_as_field(tag, buf);
        }
    }

    fn encoded_len_as_field_repeated<'a, I>(iter: I, tag: NonZeroU32) -> usize
    where
        I: Iterator<Item = &'a Self>,
        Self: 'a,
    {
        iter.map(|i| i.encoded_len_as_field(tag)).sum()
    }
}

/// Extension trait to make generic code using protobuf messages easier to write,
/// by avoiding the need to explicitly spell out the wire type in the macro.
pub trait Proto: ProtoEncode {
    /// Merge this type. For messages this will consume the buffer, setting each tag respectively.
    /// For scalar values this will decode the next value and set `self` to it. This is different
    /// to `Message::merge` in `prost`, which does not understand scalar types at all.
    fn merge_self(
        &mut self,
        wire_type: WireType,
        buf: &mut dyn bytes::Buf,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError>;
}

pub trait ProtoMergeRepeated: Proto + ProtoEncodeRepeated {
    fn merge_repeated<T>(
        values: &mut T,
        wire_type: WireType,
        buf: &mut dyn bytes::Buf,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError>
    where
        T: Extend<Self>,
        Self: Sized;
}

impl<This> ProtoMergeRepeated for This
where
    This: IsMessage + Proto + Default,
{
    fn merge_repeated<T>(
        values: &mut T,
        wire_type: WireType,
        buf: &mut dyn bytes::Buf,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError>
    where
        T: Extend<Self>,
        Self: Sized,
    {
        let mut inner = Self::default();
        inner.merge_self(wire_type, buf, ctx)?;

        values.extend(std::iter::once(inner));

        Ok(())
    }
}

pub struct MapExtend<T, F> {
    inner: T,
    func: F,
}

impl<T, F> MapExtend<T, F> {
    pub fn new(inner: T, func: F) -> Self {
        MapExtend { inner, func }
    }
}

impl<T, F, I, O> Extend<I> for MapExtend<&'_ mut T, F>
where
    T: Extend<O>,
    F: FnMut(I) -> O,
{
    fn extend<Iter: IntoIterator<Item = I>>(&mut self, iter: Iter) {
        self.inner.extend(iter.into_iter().map(&mut self.func));
    }
}

pub trait IsDefault {
    fn is_default(&self) -> bool {
        false
    }
}

pub trait IsMessage {}

pub trait ProtoOneof: IsMessage {
    fn variant<F, T>(&self, func: F) -> T
    where
        F: FnOnce(&(dyn ProtoEncode + '_), NonZeroU32) -> T;
    fn exec_merge<F, T>(&mut self, tag: NonZeroU32, func: F) -> Option<T>
    where
        F: FnOnce(&mut (dyn Proto + '_)) -> T;
}

impl<T> ProtoEncode for Option<T>
where
    T: ProtoEncode,
{
    fn encode_as_field(&self, tag: NonZeroU32, buf: &mut dyn bytes::BufMut) {
        match self {
            None => {}
            Some(v) => v.encode_as_field(tag, buf),
        }
    }

    fn encoded_len_as_field(&self, tag: NonZeroU32) -> usize {
        match self {
            None => 0,
            Some(v) => v.encoded_len_as_field(tag),
        }
    }
}

impl<T> Proto for Option<T>
where
    T: Proto + Default,
{
    fn merge_self(
        &mut self,
        wire_type: WireType,
        buf: &mut dyn bytes::Buf,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError> {
        let mut cur = self.take().unwrap_or_default();

        cur.merge_self(wire_type, buf, ctx)?;

        *self = Some(cur);

        Ok(())
    }
}

impl<T> IsDefault for Option<T> {
    fn is_default(&self) -> bool {
        self.is_none()
    }
}

pub trait ProtoMap {
    type Key: Proto;
    type Value: Proto;

    type Iter<'a>: Iterator<Item = (&'a Self::Key, &'a Self::Value)> + 'a
    where
        Self: 'a;

    fn iter(&self) -> Self::Iter<'_>;
    fn insert(&mut self, k: Self::Key, v: Self::Value);
}

impl<T, K, V> ProtoMap for T
where
    for<'a> &'a T: IntoIterator<Item = (&'a K, &'a V)>,
    T: Extend<(K, V)>,
    K: Proto,
    V: Proto,
{
    type Key = K;
    type Value = V;

    type Iter<'a>
    where
        Self: 'a,
    = <&'a Self as IntoIterator>::IntoIter;

    fn iter(&self) -> Self::Iter<'_> {
        self.into_iter()
    }

    fn insert(&mut self, k: Self::Key, v: Self::Value) {
        self.extend(std::iter::once((k, v)));
    }
}

pub trait ProtoRepeated: Extend<Self::Item> {
    type Item: Proto;
    type Iter<'a>: ExactSizeIterator<Item = &'a Self::Item> + 'a
    where
        Self: 'a;

    fn iter(&self) -> Self::Iter<'_>;
}

pub trait IntoExactSizeIterator: IntoIterator {
    type IntoExactSizeIter: ExactSizeIterator<Item = Self::Item>;

    fn into_exact_size_iter(self) -> Self::IntoExactSizeIter;
}

impl<T> IntoExactSizeIterator for T
where
    T: IntoIterator,
    T::IntoIter: ExactSizeIterator,
{
    type IntoExactSizeIter = <T as IntoIterator>::IntoIter;
    fn into_exact_size_iter(self) -> Self::IntoExactSizeIter {
        self.into_iter()
    }
}

impl<T, Item> ProtoRepeated for T
where
    T: Extend<Item>,
    Item: Proto,
    for<'a> &'a T: IntoExactSizeIterator<Item = &'a Item>,
{
    type Item = Item;
    type Iter<'a>
    where
        Self: 'a,
    = <&'a T as IntoExactSizeIterator>::IntoExactSizeIter;

    fn iter(&self) -> Self::Iter<'_> {
        self.into_exact_size_iter()
    }
}

/// Minimal set of methods needed to derive a `prost::Message` implementation for `T: ProtoStruct`.
pub trait ProtoStruct: IsMessage {
    type Fields<'a>: IntoIterator<Item = (NonZeroU32, &'a (dyn ProtoEncode + 'a))> + 'a
    where
        Self: 'a;

    fn fields(&self) -> Self::Fields<'_>;
}

pub trait ProtoStructMut: ProtoStruct {
    fn field_mut(&mut self, tag: NonZeroU32) -> Option<&mut (dyn Proto + '_)>;
}

pub trait ProtoScalar: IsDefault + Proto + Clone + Default + Sized {
    const DEFAULT_FIXED: Fixed;
    const DEFAULT_VARINT: Varint;
    const DEFAULT_ENCODING: ScalarEncoding =
        ScalarEncoding::new(ScalarEncodingKind::Varint(Some(Self::DEFAULT_VARINT)));

    fn from_value(other: Value) -> Option<Self>;
    fn to_value(&self) -> Value;
}

impl<T> ProtoEncode for T
where
    T: prost::Message + IsMessage,
{
    fn encode_as_field(&self, tag: NonZeroU32, mut buf: &mut dyn bytes::BufMut) {
        prost::encoding::message::encode(tag.get(), self, &mut buf);
    }

    fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
        prost::encoding::message::encoded_len(tag.get(), self)
    }
}

impl<T> Proto for T
where
    T: prost::Message + IsMessage,
{
    fn merge_self(
        &mut self,
        wire_type: WireType,
        mut buf: &mut dyn bytes::Buf,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError> {
        prost::encoding::message::merge(wire_type, self, &mut buf, ctx)
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Value {
    Int(i128),
    Float(f64),
}

impl Value {
    fn float(self) -> Option<f64> {
        match self {
            Self::Int(_) => None,
            Self::Float(f) => Some(f),
        }
    }

    fn bool(self) -> Option<bool> {
        self.int::<u8>().and_then(|i| match i {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        })
    }

    fn int<T: TryFrom<i128>>(self) -> Option<T> {
        match self {
            Self::Int(i) => i.try_into().ok(),
            Self::Float(_) => None,
        }
    }
}

impl<T> From<T> for Value
where
    T: Into<i128>,
{
    fn from(other: T) -> Self {
        Self::Int(other.into())
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub enum Fixed {
    /// 32-bit floating point number.
    Float,
    /// 64-bit floating point number.
    Double,
    /// 32-bit fixed-width unsigned integer.
    Fixed32,
    /// 64-bit fixed-width unsigned integer.
    Fixed64,
    /// 32-bit fixed-width signed integer.
    SFixed32,
    /// 64-bit fixed-width signed integer.
    SFixed64,
}

impl From<Fixed> for WireType {
    fn from(other: Fixed) -> Self {
        match other {
            Fixed::Float | Fixed::Fixed32 | Fixed::SFixed32 => WireType::ThirtyTwoBit,
            Fixed::Double | Fixed::Fixed64 | Fixed::SFixed64 => WireType::SixtyFourBit,
        }
    }
}

impl Fixed {
    fn read<B>(&self, buf: &mut B) -> Value
    where
        B: bytes::Buf + ?Sized,
    {
        match self {
            Self::Float => Value::Float(buf.get_f32_le() as f64),
            Self::Double => Value::Float(buf.get_f64_le()),
            Self::Fixed32 => buf.get_u32_le().into(),
            Self::Fixed64 => buf.get_u64_le().into(),
            Self::SFixed32 => buf.get_i32_le().into(),
            Self::SFixed64 => buf.get_i64_le().into(),
        }
    }

    fn write<B>(&self, value: Value, buf: &mut B)
    where
        B: bytes::BufMut + ?Sized,
    {
        match (self, value) {
            (Self::Float, Value::Float(f)) => buf.put_f32_le(f as _),
            (Self::Double, Value::Float(f)) => buf.put_f64_le(f),
            (Self::Fixed32, Value::Int(i)) => buf.put_u32_le(i as _),
            (Self::Fixed64, Value::Int(i)) => buf.put_u64_le(i as _),
            (Self::SFixed32, Value::Int(i)) => buf.put_i32_le(i as _),
            (Self::SFixed64, Value::Int(i)) => buf.put_i64_le(i as _),
            _ => panic!("Invalid encoding"),
        }
    }

    fn width(&self) -> usize {
        match self {
            Self::Float | Self::Fixed32 | Self::SFixed32 => 4,
            Self::Double | Self::Fixed64 | Self::SFixed64 => 8,
        }
    }

    fn encoded_len(&self, tag: NonZeroU32) -> usize {
        prost::encoding::key_len(tag.get()) + self.width()
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub enum Varint {
    /// Boolean
    Bool,
    /// Signed integer with less-efficient encoding of negative numbers.
    I32,
    /// Signed integer with less-efficient encoding of negative numbers.
    I64,
    /// Signed integer with more-efficient encoding of negative numbers at the expense of slightly
    /// less-efficient encoding overall.
    SI32,
    /// Signed integer with more-efficient encoding of negative numbers at the expense of slightly
    /// less-efficient encoding overall.
    SI64,
    /// Unsigned integer.
    U32,
    /// Unsigned integer.
    U64,
}

impl Varint {
    fn parse_u64_varint(&self, val: u64) -> Value {
        match self {
            Self::Bool => if val == 0 { 0i128 } else { 1i128 }.into(),
            Self::I32 => (val as i32).into(),
            Self::I64 => (val as i64).into(),
            Self::SI32 => {
                let val = val as u32;
                (((val >> 1) as i32) ^ (-((val & 1) as i32))).into()
            }
            Self::SI64 => (((val >> 1) as i64) ^ (-((val & 1) as i64))).into(),
            Self::U32 => (val as u32).into(),
            Self::U64 => (val as u64).into(),
        }
    }

    fn make_u64_varint(&self, val: Value) -> u64 {
        match (self, val) {
            (Self::Bool, Value::Int(val)) => {
                if val == 0 {
                    0
                } else {
                    1
                }
            }
            (Self::I32, Value::Int(val)) => val as i32 as u64,
            (Self::I64, Value::Int(val)) => val as i64 as u64,
            (Self::SI32, Value::Int(val)) => ((val << 1) ^ (val >> 31)) as u32 as u64,
            (Self::SI64, Value::Int(val)) => ((val << 1) ^ (val >> 63)) as u64,
            (Self::U32, Value::Int(val)) => val as u32 as u64,
            (Self::U64, Value::Int(val)) => val as u64,
            _ => panic!("Invalid encoding"),
        }
    }

    fn width(&self, value: Value) -> usize {
        prost::encoding::encoded_len_varint(self.make_u64_varint(value))
    }

    fn encoded_len(&self, tag: NonZeroU32, value: Value) -> usize {
        prost::encoding::key_len(tag.get()) + self.width(value)
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub struct ScalarEncoding {
    pub default: Option<i128>,
    pub kind: ScalarEncodingKind,
    pub packed: bool,
}

impl ScalarEncoding {
    pub const fn new(kind: ScalarEncodingKind) -> Self {
        Self {
            default: None,
            kind,
            packed: true,
        }
    }
}

impl<T> From<T> for ScalarEncoding
where
    T: Into<ScalarEncodingKind>,
{
    fn from(other: T) -> Self {
        Self::new(other.into())
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub enum ScalarEncodingKind {
    /// Explicitly specify fixed-width encoding (`None` is default for this type).
    Fixed(Option<Fixed>),
    /// Explicitly specify variable-width encoding (`None` is default for this type).
    Varint(Option<Varint>),
}

impl From<Varint> for ScalarEncodingKind {
    fn from(other: Varint) -> Self {
        Self::Varint(Some(other))
    }
}

impl From<Fixed> for ScalarEncodingKind {
    fn from(other: Fixed) -> Self {
        Self::Fixed(Some(other))
    }
}

#[derive(Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Copy, Clone)]
#[repr(transparent)]
pub struct MappedInt<T, E = DefaultEncoding<T>>(pub T, pub PhantomData<E>);

impl<T, E> Borrow<T> for MappedInt<T, E> {
    fn borrow(&self) -> &T {
        &self.0
    }
}

impl<T, E> Borrow<T> for &'_ MappedInt<T, E> {
    fn borrow(&self) -> &T {
        &self.0
    }
}

impl<T, E> MappedInt<T, E> {
    pub fn new(inner: T) -> Self {
        Self(inner, Default::default())
    }

    pub fn from_ref(v: &T) -> &Self {
        // Safe due to `repr(transparent)`
        unsafe { std::mem::transmute(v) }
    }

    pub fn from_mut(v: &mut T) -> &mut Self {
        // Safe due to `repr(transparent)`
        unsafe { std::mem::transmute(v) }
    }
}

impl<T, E> From<T> for MappedInt<T, E> {
    fn from(other: T) -> Self {
        Self::new(other)
    }
}

impl<T, E> MappedInt<T, E>
where
    T: ProtoScalar,
    E: Encoding,
{
    fn packed_len<I, B>(iter: I) -> usize
    where
        I: ExactSizeIterator<Item = B>,
        B: Borrow<T>,
    {
        match E::ENCODING.kind {
            ScalarEncodingKind::Varint(varint) => iter
                .map(|i| {
                    varint
                        .unwrap_or(T::DEFAULT_VARINT)
                        .width(i.borrow().to_value())
                })
                .sum(),
            ScalarEncodingKind::Fixed(fixed) => {
                fixed.unwrap_or(T::DEFAULT_FIXED).width() * iter.len()
            }
        }
    }

    pub fn encode_as_field_repeated<I, B>(iter: I, tag: NonZeroU32, mut buf: &mut dyn bytes::BufMut)
    where
        I: ExactSizeIterator<Item = B> + Clone,
        B: Borrow<T>,
    {
        if E::ENCODING.packed {
            let len = Self::packed_len(iter.clone());

            prost::encoding::encode_key(tag.get(), WireType::LengthDelimited, &mut buf);
            prost::encoding::encode_varint(len as u64, &mut buf);

            match E::ENCODING.kind {
                ScalarEncodingKind::Varint(varint) => {
                    let varint = varint.unwrap_or(T::DEFAULT_VARINT);

                    for value in iter {
                        prost::encoding::encode_varint(
                            varint.make_u64_varint(value.borrow().to_value()),
                            &mut buf,
                        );
                    }
                }
                ScalarEncodingKind::Fixed(fixed) => {
                    let fixed = fixed.unwrap_or(T::DEFAULT_FIXED);

                    for value in iter {
                        fixed.write(value.borrow().to_value(), buf)
                    }
                }
            }
        } else {
            for i in iter {
                i.borrow().encode_as_field(tag, buf);
            }
        }
    }

    pub fn encoded_len_as_field_repeated<I, B>(iter: I, tag: NonZeroU32) -> usize
    where
        I: ExactSizeIterator<Item = B>,
        B: Borrow<T>,
    {
        if E::ENCODING.packed {
            let len = Self::packed_len(iter);

            prost::encoding::key_len(tag.get())
                + prost::encoding::encoded_len_varint(len as u64)
                + len
        } else {
            iter.map(|i| i.borrow().encoded_len_as_field(tag)).sum()
        }
    }
}

pub trait Encoding: Default {
    const ENCODING: ScalarEncoding;
}

pub struct DefaultEncoding<T>(pub PhantomData<T>);

impl<T> Default for DefaultEncoding<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T> Encoding for DefaultEncoding<T>
where
    T: ProtoScalar,
{
    const ENCODING: ScalarEncoding = T::DEFAULT_ENCODING;
}

impl<T, E> ProtoEncodeRepeated for MappedInt<T, E>
where
    T: ProtoScalar,
    E: Encoding,
{
    fn encode_as_field_repeated<'a, I>(iter: I, tag: NonZeroU32, buf: &mut dyn bytes::BufMut)
    where
        I: ExactSizeIterator<Item = &'a Self> + Clone,
        Self: 'a,
    {
        Self::encode_as_field_repeated(iter, tag, buf)
    }

    fn encoded_len_as_field_repeated<'a, I>(iter: I, tag: NonZeroU32) -> usize
    where
        I: ExactSizeIterator<Item = &'a Self>,
        Self: 'a,
    {
        Self::encoded_len_as_field_repeated(iter, tag)
    }
}

impl<I, E> ProtoMergeRepeated for MappedInt<I, E>
where
    I: ProtoScalar,
    E: Encoding,
{
    fn merge_repeated<T>(
        values: &mut T,
        wire_type: WireType,
        mut buf: &mut dyn bytes::Buf,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError>
    where
        T: Extend<Self>,
        Self: Sized,
    {
        use std::iter;

        let expected_wire_type = match E::ENCODING.kind {
            ScalarEncodingKind::Varint(_) => WireType::Varint,
            ScalarEncodingKind::Fixed(fixed) => fixed.unwrap_or(I::DEFAULT_FIXED).into(),
        };

        match wire_type {
            WireType::LengthDelimited => {
                let len = prost::encoding::decode_varint(&mut buf)?;
                let remaining = buf.remaining();

                if len > remaining as u64 {
                    return Err(prost::DecodeError::new("buffer underflow"));
                }

                let limit = remaining - len as usize;

                while buf.remaining() > limit {
                    let mut value = Self::default();
                    value.merge_self(expected_wire_type, buf, ctx.clone())?;
                    values.extend(iter::once(value));
                }

                if buf.remaining() != limit {
                    return Err(prost::DecodeError::new("delimited length exceeded"));
                }

                Ok(())
            }
            _ => {
                let mut inner = Self::default();
                inner.merge_self(expected_wire_type, buf, ctx)?;

                values.extend(iter::once(inner));

                Ok(())
            }
        }
    }
}

impl<T, E> IsDefault for MappedInt<T, E>
where
    T: ProtoScalar,
    E: Encoding,
{
    fn is_default(&self) -> bool {
        match (E::ENCODING.default, self.0.to_value()) {
            (Some(default), Value::Int(inner)) => default == inner,
            _ => self.0.is_default(),
        }
    }
}

impl<T, E> ProtoEncode for MappedInt<T, E>
where
    T: ProtoScalar,
    E: Encoding,
{
    fn encode_as_field(&self, tag: NonZeroU32, mut buf: &mut dyn bytes::BufMut) {
        if !self.0.is_default() {
            match E::ENCODING.kind {
                ScalarEncodingKind::Varint(varint) => {
                    prost::encoding::encode_key(tag.get(), WireType::Varint, &mut buf);
                    prost::encoding::encode_varint(
                        varint
                            .unwrap_or(T::DEFAULT_VARINT)
                            .make_u64_varint(self.0.to_value()),
                        &mut buf,
                    )
                }
                ScalarEncodingKind::Fixed(fixed) => {
                    let fixed = fixed.unwrap_or(T::DEFAULT_FIXED);

                    prost::encoding::encode_key(tag.get(), fixed.into(), &mut buf);

                    fixed.write(self.0.to_value(), buf)
                }
            }
        }
    }

    fn encoded_len_as_field(&self, tag: NonZeroU32) -> usize {
        if self.0.is_default() {
            0
        } else {
            match E::ENCODING.kind {
                ScalarEncodingKind::Varint(varint) => varint
                    .unwrap_or(T::DEFAULT_VARINT)
                    .encoded_len(tag, self.0.to_value()),
                ScalarEncodingKind::Fixed(fixed) => {
                    fixed.unwrap_or(T::DEFAULT_FIXED).encoded_len(tag)
                }
            }
        }
    }
}

impl<T, E> Proto for MappedInt<T, E>
where
    T: ProtoScalar,
    E: Encoding,
{
    fn merge_self(
        &mut self,
        wire_type: WireType,
        mut buf: &mut dyn bytes::Buf,
        _ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError> {
        self.0 = match E::ENCODING.kind {
            ScalarEncodingKind::Varint(varint) => {
                prost::encoding::check_wire_type(WireType::Varint, wire_type)?;

                T::from_value(
                    varint
                        .unwrap_or(T::DEFAULT_VARINT)
                        .parse_u64_varint(prost::encoding::decode_varint(&mut buf)?),
                )
                .ok_or_else(|| prost::DecodeError::new("Type mismatch"))?
            }
            ScalarEncodingKind::Fixed(fixed) => {
                let fixed = fixed.unwrap_or(T::DEFAULT_FIXED);
                prost::encoding::check_wire_type(fixed.into(), wire_type)?;

                T::from_value(fixed.read(&mut buf))
                    .ok_or_else(|| prost::DecodeError::new("Type mismatch"))?
            }
        };

        Ok(())
    }
}

macro_rules! impl_is_default {
    ($($t:ty),*) => {
        $(
            impl $crate::IsDefault for $t {
                fn is_default(&self) -> bool {
                    $crate::generic::default::is_default(self)
                }
            }
        )*
    };
}

impl_is_default!(bool, u8, u16, u32, u64, i8, i16, i32, i64, usize, isize, f32, f64);

impl_protoscalar!(
    bool,
    (|v: Value| v.bool(), |v: bool| Value::Int((v as u64).into())),
    Fixed::Fixed32,
    Varint::U32
);
impl_protoscalar!(u8, Fixed::Fixed32, Varint::U32);
impl_protoscalar!(u16, Fixed::Fixed32, Varint::U32);
impl_protoscalar!(u32, Fixed::Fixed32, Varint::U32);
impl_protoscalar!(u64, Fixed::Fixed64, Varint::U64);
impl_protoscalar!(i8, Fixed::SFixed32, Varint::I32);
impl_protoscalar!(i16, Fixed::SFixed32, Varint::I32);
impl_protoscalar!(i32, Fixed::SFixed32, Varint::I32);
impl_protoscalar!(i64, Fixed::SFixed64, Varint::I64);
impl_protoscalar!(
    usize,
    (|v: Value| v.int(), |v: usize| Value::Int((v as u64).into())),
    Fixed::Fixed64,
    Varint::U64
);
impl_protoscalar!(
    isize,
    (
        |v: Value| v.int::<i64>().map(|i| i as _),
        |v: isize| Value::Int((v as i64).into())
    ),
    Fixed::SFixed64,
    Varint::I64
);
impl_protoscalar!(
    f32,
    (
        |v: Value| v.float().map(|f| f as f32),
        |v| Value::Float(v as f64)
    ),
    Fixed::Float,
    Varint::I32,
    ScalarEncoding::new(ScalarEncodingKind::Fixed(Some(Self::DEFAULT_FIXED)))
);
impl_protoscalar!(
    f64,
    (|v: Value| v.float(), |v| Value::Float(v)),
    Fixed::Double,
    Varint::I64,
    ScalarEncoding::new(ScalarEncodingKind::Fixed(Some(Self::DEFAULT_FIXED)))
);

impl_proto_for_message!(impl Proto for ());
impl_proto_for_message!(impl Proto for bytes::Bytes);
impl_proto_for_message!(impl Proto for String);

impl_proto_for_protomap!(
    impl<K, V> Proto for BTreeMap<K, V>
    where
        K: Proto,
        K: Default,
        K: std::cmp::Ord,
        V: Proto,
        V: Default,
        V: PartialEq,
    where
        K: 'static,
        V: 'static
);
impl_proto_for_protomap!(
    impl<K, V> Proto for HashMap<K, V>
    where
        K: Proto,
        K: Default,
        K: Eq,
        K: Hash,
        V: Proto,
        V: Default,
        V: PartialEq,
    where
        K: 'static,
        V: 'static
);

impl_proto_for_protorepeated!(impl<T> Proto for Vec<T> where T: ProtoMergeRepeated, where T: 'static);
impl_proto_for_protorepeated!(
    impl<T> Proto for HashSet<T>
    where
        T: Eq,
        T: Hash,
        T: ProtoMergeRepeated,
    where
        T: 'static
);
impl_proto_for_protorepeated!(
    impl<T> Proto for BTreeSet<T>
    where
        T: Ord,
        T: ProtoMergeRepeated,
        T: Default,
    where
        T: 'static
);

#[cfg(feature = "smallvec")]
impl_proto_for_protorepeated!(
    impl<T> Proto for smallvec::SmallVec<T>
    where
        T: smallvec::Array,
        <T as smallvec::Array>::Item: ProtoMergeRepeated,
    where
        T: 'static
);

#[cfg(feature = "arrayvec")]
impl_proto_for_protorepeated!(
    impl<T; const SIZE: usize> Proto for arrayvec::ArrayVec<T, SIZE>
    where
        T: ProtoMergeRepeated,
    where
        T: 'static
);
