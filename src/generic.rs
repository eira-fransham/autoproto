//! Because of the orphan rule, most traits cannot have generic implementations for
//! any `T` that implements a certain trait. Therefore, we can instead have these
//! generic implementations written as free functions and have the derive macro
//! generate calls to them. This means we can reduce the amount of generated code
//! significantly.
//!
//! The submodules are named for the traits required, and the free functions are
//! prefixed with the trait that the method is found on.

pub use wrapper::Wrapper;

mod wrapper {
    use crate::{Clear, IsDefault, Proto, ProtoEncode};
    use std::ops::{Deref, DerefMut};

    /// Because of the orphan rule, if we want to implement a trait on `&T` or `&mut T`
    /// while also implementing it on `T: SomeTrait`, we need to have a custom wrapper
    /// type.
    #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    pub struct Wrapper<T>(pub T);

    impl<T> Deref for Wrapper<T>
    where
        T: Deref,
    {
        type Target = T::Target;

        fn deref(&self) -> &Self::Target {
            &*self.0
        }
    }

    impl<T> DerefMut for Wrapper<T>
    where
        T: DerefMut,
    {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut *self.0
        }
    }

    impl<T> Clear for Wrapper<&'_ mut T>
    where
        T: Clear,
    {
        fn clear(&mut self) {
            (**self).clear()
        }
    }

    impl<T> ProtoEncode for Wrapper<T>
    where
        T: Deref,
        T::Target: ProtoEncode,
    {
        fn encode_as_field(&self, tag: std::num::NonZeroU32, buf: &mut dyn prost::bytes::BufMut) {
            (**self).encode_as_field(tag, buf)
        }

        fn encoded_len_as_field(&self, tag: std::num::NonZeroU32) -> usize {
            (**self).encoded_len_as_field(tag)
        }
    }

    impl<T> IsDefault for Wrapper<T>
    where
        T: Deref,
        T::Target: IsDefault,
    {
        fn is_default(&self) -> bool {
            (**self).is_default()
        }
    }

    impl<T> Proto for Wrapper<T>
    where
        T: DerefMut,
        T::Target: Proto,
        Self: Clear,
    {
        fn merge_self(
            &mut self,
            wire_type: prost::encoding::WireType,
            buf: &mut dyn prost::bytes::Buf,
            ctx: prost::encoding::DecodeContext,
        ) -> Result<(), prost::DecodeError> {
            (**self).merge_self(wire_type, buf, ctx)
        }
    }
}

pub mod protostruct {
    use crate::{ProtoStruct, ProtoStructMut};
    use prost::{
        bytes::{Buf, BufMut},
        encoding::{DecodeContext, WireType},
        DecodeError,
    };
    use std::num::NonZeroU32;

    pub fn message_encode_to_vec<T: ProtoStruct>(this: &T) -> Vec<u8> {
        let mut out = Vec::with_capacity(message_encoded_len(this));
        message_encode_raw(this, &mut out);

        out
    }

    pub fn message_merge<T: ProtoStructMut, B: Buf>(
        this: &mut T,
        mut buf: B,
    ) -> Result<(), DecodeError> {
        let ctx = DecodeContext::default();
        while buf.has_remaining() {
            let (tag, wire_type) = prost::encoding::decode_key(&mut buf)?;
            message_merge_field(this, tag, wire_type, &mut buf, ctx.clone())?;
        }
        Ok(())
    }

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

    pub fn protoencode_encode_as_field<T: ProtoStruct>(
        this: &T,
        tag: NonZeroU32,
        mut buf: &mut dyn prost::bytes::BufMut,
    ) {
        let len = message_encoded_len(this);
        let buf = &mut buf;

        prost::encoding::encode_key(tag.get(), prost::encoding::WireType::LengthDelimited, buf);
        prost::encoding::encode_varint(len as u64, buf);
        message_encode_raw(this, buf)
    }

    pub fn protoencode_encoded_len_as_field<T: ProtoStruct>(this: &T, tag: NonZeroU32) -> usize {
        let len = message_encoded_len(this);
        prost::encoding::key_len(tag.get()) + prost::encoding::encoded_len_varint(len as u64) + len
    }

    pub fn proto_merge_self<T: ProtoStructMut>(
        this: &mut T,
        wire_type: WireType,
        mut buf: &mut dyn prost::bytes::Buf,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError> {
        prost::encoding::check_wire_type(WireType::LengthDelimited, wire_type)?;
        prost::encoding::merge_loop(this, &mut buf, ctx, |this, buf, ctx| {
            let (tag, wire_type) = prost::encoding::decode_key(buf)?;
            if let Some(field) = NonZeroU32::new(tag).and_then(|tag| this.field_mut(tag)) {
                field.merge_self(wire_type, buf, ctx)
            } else {
                prost::encoding::skip_field(wire_type, tag, buf, ctx)
            }
        })
    }
}

pub mod clear {
    use crate::Clear;

    pub fn message_clear<T: Clear>(this: &mut T) {
        this.clear()
    }
}

pub mod default {
    pub fn is_default<T: Default + PartialEq>(this: &T) -> bool {
        *this == Default::default()
    }
}

pub mod proto {
    use crate::Proto;
    use prost::{
        bytes::Buf,
        encoding::{DecodeContext, WireType},
        DecodeError,
    };

    pub fn protomergerepeated_merge_repeated<This, T>(
        values: &mut T,
        wire_type: WireType,
        buf: &mut dyn Buf,
        ctx: DecodeContext,
    ) -> Result<(), DecodeError>
    where
        T: Extend<This>,
        This: Proto + Default,
    {
        let mut inner = This::default();
        inner.merge_self(wire_type, buf, ctx)?;

        values.extend(std::iter::once(inner));

        Ok(())
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
        this.variant(|inner, tag| inner.encode_as_field(tag, buf))
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
        this.variant(|inner, tag| inner.encoded_len_as_field(tag))
    }
}

pub mod protoscalar {
    use crate::{Encoding, MappedInt, Proto as _, ProtoEncode as _, ProtoScalar};
    use prost::{
        bytes::{Buf, BufMut},
        encoding::{DecodeContext, WireType},
        DecodeError,
    };
    use std::num::NonZeroU32;

    pub fn protoencode_encode_as_field<T: ProtoScalar, E: Encoding>(
        this: &T,
        tag: NonZeroU32,
        buf: &mut dyn BufMut,
    ) {
        MappedInt::<_, E>(this.clone(), Default::default()).encode_as_field(tag, buf)
    }

    pub fn protoencode_encoded_len_as_field<T: ProtoScalar, E: Encoding>(
        this: &T,
        tag: NonZeroU32,
    ) -> usize {
        MappedInt::<_, E>(this.clone(), Default::default()).encoded_len_as_field(tag)
    }

    pub fn proto_merge_self<T: ProtoScalar, E: Encoding>(
        this: &mut T,
        wire_type: WireType,
        buf: &mut dyn Buf,
        ctx: DecodeContext,
    ) -> Result<(), DecodeError> {
        let mut mapped = MappedInt::<_, E>(this.clone(), Default::default());
        mapped.merge_self(wire_type, buf, ctx)?;

        *this = mapped.0;

        Ok(())
    }
}
