//! Because of the orphan rule, most traits cannot have generic implementations for
//! any `T` that implements a certain trait. Therefore, we can instead have these
//! generic implementations written as free functions and have the derive macro
//! generate calls to them. This means we can reduce the amount of generated code
//! significantly.
//!
//! The submodules are named for the traits required, and the free functions are
//! prefixed with the trait that the method is found on.

pub mod protostruct {
    use crate::{ProtoStruct, ProtoStructMut};
    use prost::{
        bytes::{Buf, BufMut},
        encoding::{DecodeContext, WireType},
        DecodeError,
    };
    use std::num::NonZeroU32;

    pub fn message_encode_raw<T: ProtoStruct, B: BufMut>(this: &T, buf: &mut B) {
        for (tag, field) in this.fields() {
            field.encode_as_field(tag, buf)
        }
    }

    pub fn message_merge_field<T: ProtoStructMut, B: Buf>(
        this: &mut T,
        tag: u32,
        wire_type: WireType,
        buf: &mut B,
        ctx: DecodeContext,
    ) -> Result<(), DecodeError> {
        if let Some(field) = NonZeroU32::new(tag).and_then(|tag| this.field_mut(tag)) {
            field.merge_self(wire_type, buf, ctx)?;
        }

        Ok(())
    }

    pub fn message_encoded_len<T: ProtoStruct>(this: &T) -> usize {
        this.fields()
            .into_iter()
            .map(|(tag, field)| field.encoded_len_as_field(tag))
            .sum()
    }

    pub fn is_default<T: ProtoStruct>(this: &T) -> bool {
        this.fields()
            .into_iter()
            .all(|(_, field)| field.is_default())
    }
}

pub mod default {
    pub fn message_clear<T: Default>(this: &mut T) {
        *this = Default::default();
    }

    pub fn is_default<T: Default + PartialEq>(this: &T) -> bool {
        *this == Default::default()
    }
}

pub mod protooneof {
    use crate::ProtoOneof;
    use prost::{
        bytes::{Buf, BufMut},
        encoding::{DecodeContext, WireType},
        DecodeError,
    };
    use std::num::NonZeroU32;

    pub fn message_encode_raw<T: ProtoOneof, B: BufMut>(this: &T, buf: &mut B) {
        if !this.is_default() {
            let (tag, inner) = this.variant();
            inner.encode_as_field(tag, buf)
        }
    }

    pub fn message_merge_field<T: ProtoOneof, B: Buf>(
        this: &mut T,
        tag: u32,
        wire_type: WireType,
        buf: &mut B,
        ctx: DecodeContext,
    ) -> Result<(), DecodeError> {
        this.exec_merge(
            NonZeroU32::new(tag).ok_or_else(|| DecodeError::new("Invalid tag: 0"))?,
            |val| val.merge_self(wire_type, buf, ctx.clone()),
        );

        Ok(())
    }

    pub fn message_encoded_len<T: ProtoOneof>(this: &T) -> usize {
        let (tag, inner) = this.variant();
        inner.encoded_len_as_field(tag)
    }
}

pub mod protoscalar {
    use crate::{MappedInt, Proto as _, ProtoEncode as _, ProtoScalar, ScalarEncoding};
    use prost::{
        bytes::{Buf, BufMut},
        encoding::{DecodeContext, WireType},
        DecodeError,
    };
    use std::num::NonZeroU32;

    pub fn protoencode_encode_as_field<const DEFAULT_ENCODING: ScalarEncoding, T: ProtoScalar>(
        this: &T,
        tag: NonZeroU32,
        buf: &mut dyn BufMut,
    ) {
        MappedInt::<DEFAULT_ENCODING, _>(this.clone()).encode_as_field(tag, buf)
    }

    pub fn protoencode_encoded_len_as_field<
        const DEFAULT_ENCODING: ScalarEncoding,
        T: ProtoScalar,
    >(
        this: &T,
        tag: NonZeroU32,
    ) -> usize {
        MappedInt::<DEFAULT_ENCODING, _>(this.clone()).encoded_len_as_field(tag)
    }

    pub fn proto_merge_self<const DEFAULT_ENCODING: ScalarEncoding, T: ProtoScalar>(
        this: &mut T,
        wire_type: WireType,
        buf: &mut dyn Buf,
        ctx: DecodeContext,
    ) -> Result<(), DecodeError> {
        let mut mapped = MappedInt::<DEFAULT_ENCODING, _>(this.clone());
        mapped.merge_self(wire_type, buf, ctx)?;

        *this = mapped.0;

        Ok(())
    }
}
