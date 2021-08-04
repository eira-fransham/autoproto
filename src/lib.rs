#![feature(const_generics, generic_associated_types)]

pub use autoproto_derive::{Message, ProtoEncode};
#[doc(hidden)]
pub use prost;

pub use prost::bytes::Bytes;

pub mod generic;
pub mod macros;

use prost::encoding::{DecodeContext, WireType};
use std::{
    borrow::{Cow, ToOwned},
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    convert::{TryFrom, TryInto},
    fmt::{self, Debug},
    hash::Hash,
    marker::PhantomData,
    num::NonZeroU32,
};

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

// This is just so we can use `Cow`. The fact that you can't use the ref capabilities of `Cow`
// without _also_ allowing conversion to an owned type is such an annoying limitation of `Cow`.
impl ToOwned for dyn Proto + '_ {
    type Owned = Box<Self>;

    fn to_owned(&self) -> Self::Owned {
        panic!("Unable to create `Box<Self>`")
    }
}

// This is just so we can use `Cow`. The fact that you can't use the ref capabilities of `Cow`
// without _also_ allowing conversion to an owned type is such an annoying limitation of `Cow`.
impl ToOwned for dyn ProtoEncode + '_ {
    type Owned = Box<Self>;

    fn to_owned(&self) -> Self::Owned {
        panic!("Unable to create `Box<Self>`")
    }
}

impl<T> ProtoEncode for PhantomData<T> {
    fn encode_as_field(&self, tag: NonZeroU32, buf: &mut dyn prost::bytes::BufMut) {
        <()>::encode_as_field(&(), tag, buf)
    }

    fn encoded_len_as_field(&self, tag: NonZeroU32) -> usize {
        <()>::encoded_len_as_field(&(), tag)
    }
}

impl<T> Proto for PhantomData<T> {
    fn merge_self(
        &mut self,
        wire_type: WireType,
        buf: &mut dyn prost::bytes::Buf,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError> {
        <()>::merge_self(&mut (), wire_type, buf, ctx)
    }
}

pub trait ProtoEncode: IsDefault {
    /// Encode this type _as a field_. This is different to encoding it as a message (which is
    /// what `prost::Message:encode_raw` does), as base types such as integers are encoded
    /// differently as fields vs as messages.
    fn encode_as_field(&self, tag: NonZeroU32, buf: &mut dyn prost::bytes::BufMut);

    /// Get the length if this type is encoded with its field tag.
    fn encoded_len_as_field(&self, tag: NonZeroU32) -> usize;
}

impl<T> ProtoEncode for &'_ T
where
    T: ProtoEncode,
{
    fn encode_as_field(&self, tag: NonZeroU32, buf: &mut dyn prost::bytes::BufMut) {
        (**self).encode_as_field(tag, buf)
    }

    fn encoded_len_as_field(&self, tag: NonZeroU32) -> usize {
        (**self).encoded_len_as_field(tag)
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
        buf: &mut dyn prost::bytes::Buf,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError>;
}

pub trait IsDefault {
    fn is_default(&self) -> bool {
        false
    }
}

pub trait ProtoOneof: IsDefault {
    fn variant(&self) -> (NonZeroU32, Cow<'_, dyn ProtoEncode>);
    fn exec_merge<F, T>(&mut self, tag: NonZeroU32, func: F) -> Option<T>
    where
        F: FnMut(&mut dyn Proto) -> T;
}

impl<T> ProtoEncode for Option<T>
where
    T: ProtoEncode,
{
    fn encode_as_field(&self, tag: NonZeroU32, buf: &mut dyn prost::bytes::BufMut) {
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
        buf: &mut dyn prost::bytes::Buf,
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
    type Iter<'a>: Iterator<Item = &'a Self::Item> + 'a
    where
        Self: 'a;

    fn iter(&self) -> Self::Iter<'_>;
}

impl<T, Item> ProtoRepeated for T
where
    T: Extend<Item>,
    Item: Proto,
    for<'a> &'a T: IntoIterator<Item = &'a Item>,
{
    type Item = Item;
    type Iter<'a>
    where
        Self: 'a,
    = <&'a T as IntoIterator>::IntoIter;

    fn iter(&self) -> Self::Iter<'_> {
        self.into_iter()
    }
}

/// Minimal set of methods needed to derive a `prost::Message` implementation for `T: ProtoStruct`.
pub trait ProtoStruct {
    type Fields<'a>: IntoIterator<Item = (NonZeroU32, Cow<'a, dyn ProtoEncode>)> + 'a
    where
        Self: 'a;

    fn fields(&self) -> Self::Fields<'_>;
}

pub trait ProtoStructMut: ProtoStruct {
    fn field_mut(&mut self, tag: NonZeroU32) -> Option<&mut dyn Proto>;
}

pub trait ProtoScalar: Clone + Default + Proto + Sized {
    const DEFAULT_FIXED: Fixed;
    const DEFAULT_VARINT: Varint;
    const DEFAULT_ENCODING: ScalarEncoding =
        ScalarEncoding::new(ScalarEncodingKind::Varint(Some(Self::DEFAULT_VARINT)));

    fn from_value(other: Value) -> Option<Self>;
    fn into_value(&self) -> Value;
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
        B: prost::bytes::Buf + ?Sized,
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
        B: prost::bytes::BufMut + ?Sized,
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

    fn encoded_len(&self, tag: NonZeroU32, value: Value) -> usize {
        use prost::encoding::*;

        match (self, value) {
            (Self::Float, Value::Float(f)) => float::encoded_len(tag.get(), &(f as f32)),
            (Self::Double, Value::Float(f)) => double::encoded_len(tag.get(), &(f as f64)),
            (Self::Fixed32, Value::Int(i)) => fixed32::encoded_len(tag.get(), &(i as u32)),
            (Self::Fixed64, Value::Int(i)) => fixed64::encoded_len(tag.get(), &(i as u64)),
            (Self::SFixed32, Value::Int(i)) => sfixed32::encoded_len(tag.get(), &(i as i32)),
            (Self::SFixed64, Value::Int(i)) => sfixed64::encoded_len(tag.get(), &(i as i64)),
            _ => panic!("Invalid encoding"),
        }
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

    fn encoded_len(&self, tag: NonZeroU32, value: Value) -> usize {
        use prost::encoding::*;

        match (self, value) {
            (Self::I32, Value::Int(i)) => int32::encoded_len(tag.get(), &(i as i32)),
            (Self::I64, Value::Int(i)) => int64::encoded_len(tag.get(), &(i as i64)),
            (Self::SI32, Value::Int(i)) => sint32::encoded_len(tag.get(), &(i as i32)),
            (Self::SI64, Value::Int(i)) => sint64::encoded_len(tag.get(), &(i as i64)),
            (Self::U32, Value::Int(i)) => uint32::encoded_len(tag.get(), &(i as u32)),
            (Self::U64, Value::Int(i)) => uint64::encoded_len(tag.get(), &(i as u64)),
            _ => panic!("Invalid encoding"),
        }
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub struct ScalarEncoding {
    pub default: Option<i128>,
    pub kind: ScalarEncodingKind,
}

impl ScalarEncoding {
    pub const fn new(kind: ScalarEncodingKind) -> Self {
        Self {
            default: None,
            kind,
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

#[derive(Debug, Copy, Clone)]
pub struct MappedInt<const ENCODING: ScalarEncoding, T>(pub T);

impl<const ENCODING: ScalarEncoding, T> IsDefault for MappedInt<ENCODING, T>
where
    T: IsDefault + ProtoScalar,
{
    fn is_default(&self) -> bool {
        match (ENCODING.default, self.0.into_value()) {
            (Some(default), Value::Int(inner)) => default == inner,
            _ => self.0.is_default(),
        }
    }
}

impl<const ENCODING: ScalarEncoding, T> ProtoEncode for MappedInt<ENCODING, T>
where
    T: ProtoScalar,
{
    fn encode_as_field(&self, tag: NonZeroU32, mut buf: &mut dyn prost::bytes::BufMut) {
        match ENCODING.kind {
            ScalarEncodingKind::Varint(varint) => {
                prost::encoding::encode_key(tag.get(), WireType::Varint, &mut buf);
                prost::encoding::encode_varint(
                    varint
                        .unwrap_or(T::DEFAULT_VARINT)
                        .make_u64_varint(self.0.into_value()),
                    &mut buf,
                )
            }
            ScalarEncodingKind::Fixed(fixed) => {
                let fixed = fixed.unwrap_or(T::DEFAULT_FIXED);

                prost::encoding::encode_key(tag.get(), fixed.into(), &mut buf);

                fixed.write(self.0.into_value(), buf)
            }
        }
    }

    fn encoded_len_as_field(&self, tag: NonZeroU32) -> usize {
        match ENCODING.kind {
            ScalarEncodingKind::Varint(varint) => varint
                .unwrap_or(T::DEFAULT_VARINT)
                .encoded_len(tag, self.0.into_value()),
            ScalarEncodingKind::Fixed(fixed) => fixed
                .unwrap_or(T::DEFAULT_FIXED)
                .encoded_len(tag, self.0.into_value()),
        }
    }
}

impl<const ENCODING: ScalarEncoding, T> Proto for MappedInt<ENCODING, T>
where
    T: ProtoScalar,
{
    fn merge_self(
        &mut self,
        wire_type: WireType,
        mut buf: &mut dyn prost::bytes::Buf,
        _ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError> {
        self.0 = match ENCODING.kind {
            ScalarEncodingKind::Varint(varint) => {
                prost::encoding::check_wire_type(WireType::Varint, wire_type)?;

                T::from_value(
                    varint
                        .unwrap_or(T::DEFAULT_VARINT)
                        .parse_u64_varint(prost::encoding::decode_varint(&mut buf)?),
                )
                .ok_or(prost::DecodeError::new("Type mismatch"))?
            }
            ScalarEncodingKind::Fixed(fixed) => {
                let fixed = fixed.unwrap_or(T::DEFAULT_FIXED);
                prost::encoding::check_wire_type(fixed.into(), wire_type)?;

                T::from_value(fixed.read(&mut buf))
                    .ok_or(prost::DecodeError::new("Type mismatch"))?
            }
        };

        Ok(())
    }
}

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
impl_proto_for_message!(impl Proto for prost::bytes::Bytes);
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

impl_proto_for_protorepeated!(impl<T> Proto for Vec<T> where T: Proto, T: Default, where T: 'static);
impl_proto_for_protorepeated!(
    impl<T> Proto for HashSet<T>
    where
        T: Eq,
        T: Hash,
        T: Proto,
        T: Default,
    where
        T: 'static
);
impl_proto_for_protorepeated!(
    impl<T> Proto for BTreeSet<T>
    where
        T: Ord,
        T: Proto,
        T: Default,
    where
        T: 'static
);

#[cfg(feature = "smallvec")]
impl_proto_for_protorepeated!(
    impl<T> Proto for smallvec::SmallVec<T>
    where
        T: smallvec::Array,
        <T as smallvec::Array>::Item: Proto,
        <T as smallvec::Array>::Item: Default,
    where
        T: 'static
);
#[cfg(feature = "arrayvec")]
impl_proto_for_protorepeated!(
    impl<T; const SIZE: usize> Proto for arrayvec::ArrayVec<T, SIZE>
    where
        T: Proto,
        T: Default,
    where
        T: 'static
);
