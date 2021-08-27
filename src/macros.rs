#[macro_export]
macro_rules! impl_proto_for_bytes {
    (
        impl$(<$($pname:ident),*$(; $(const $cname:ident : $cty:ty),*)?>)? Proto for $t:ty
        $(where $($bounded:ty : $bound:path,)* $(where $($lbounded:ty : $lbound:lifetime),*)?)?
    ) => {
        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::ProtoEncode for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn encode_as_field(&self, tag: NonZeroU32, mut buf: &mut dyn bytes::BufMut) {
                let len = <Self as ::core::convert::AsRef<[u8]>>::as_ref(self).len();

                $crate::prost::encoding::encode_key(tag.get(), WireType::LengthDelimited, &mut buf);
                $crate::prost::encoding::encode_varint(len as u64, &mut buf);
                buf.put_slice(<Self as ::core::convert::AsRef<[u8]>>::as_ref(self));
            }

            fn encoded_len_as_field(&self, tag: NonZeroU32) -> usize {
                let len = <Self as ::core::convert::AsRef<[u8]>>::as_ref(self).len();

                $crate::prost::encoding::key_len(tag.get())
                    + $crate::prost::encoding::encoded_len_varint(len as u64)
                    + len
            }
        }

        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::Proto for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn merge_self(
                &mut self,
                wire_type: $crate::prost::encoding::WireType,
                mut buf: &mut dyn $crate::prost::bytes::Buf,
                _ctx: $crate::prost::encoding::DecodeContext,
            ) -> Result<(), $crate::prost::DecodeError> {
                use crate::bytes::Buf as _;

                $crate::prost::encoding::check_wire_type(WireType::LengthDelimited, wire_type)?;
                let len = $crate::prost::encoding::decode_varint(&mut buf)?;
                if len > buf.remaining() as u64 {
                    return Err($crate::prost::DecodeError::new("buffer underflow"));
                }

                <&mut &mut dyn $crate::bytes::Buf as $crate::bytes::Buf>::take(
                    &mut buf,
                    len as usize,
                ).copy_to_slice(<Self as ::core::convert::AsMut<[u8]>>::as_mut(self));
                Ok(())
            }
        }

        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::IsDefault for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn is_default(&self) -> bool {
                <Self as ::core::convert::AsRef<[u8]>>::as_ref(self).is_empty()
            }
        }
    }
}

#[macro_export]
macro_rules! impl_proto_for_message {
    (
        impl$(<$($pname:ident),*$(; $(const $cname:ident : $cty:ty),*)?>)? Proto for $t:ty
        $(where $($bounded:ty : $bound:path,)* $(where $($lbounded:ty : $lbound:lifetime),*)?)?
    ) => {
        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::ProtoEncode for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, mut buf: &mut dyn $crate::prost::bytes::BufMut) {
                $crate::prost::encoding::message::encode(tag.get(), self, &mut buf);
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                $crate::prost::encoding::message::encoded_len(tag.get(), self)
            }
        }

        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::Proto for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn merge_self(
                &mut self,
                wire_type: $crate::prost::encoding::WireType,
                mut buf: &mut dyn $crate::prost::bytes::Buf,
                ctx: $crate::prost::encoding::DecodeContext,
            ) -> Result<(), $crate::prost::DecodeError> {
                $crate::prost::encoding::message::merge(wire_type, self, &mut buf, ctx)
            }
        }

        impl $crate::IsDefault for $t {
            fn is_default(&self) -> bool {
                *self == Self::default()
            }
        }
    }
}

#[macro_export]
macro_rules! impl_protoscalar {
    ($t:ty, $default_fixed:path, $default_varint:path $(, $default_encoding:expr)?) => {
        impl_protoscalar!(
            $t,
            (|v: Value| v.int(), |v: $t| Value::Int(v.into())),
            $default_fixed,
            $default_varint
            $(, $default_encoding)?
        );
    };

    ($t:ty, ($from_value:expr, $into_value:expr), $default_fixed:path, $default_varint:path $(, $default_encoding:expr)?) => {
        #[allow(clippy::all)]
        impl $crate::ProtoScalar for $t {
            const DEFAULT_FIXED: Fixed = $default_fixed;
            const DEFAULT_VARINT: Varint = $default_varint;
            $(const DEFAULT_ENCODING: ScalarEncoding = $default_encoding;)?

            fn from_value(other: Value) -> Option<Self> {
                ($from_value)(other)
            }

            fn to_value(&self) -> Value {
                ($into_value)(*self)
            }
        }

        #[allow(clippy::all)]
        impl $crate::ProtoEncode for $t {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, buf: &mut dyn $crate::prost::bytes::BufMut) {
                MappedInt::<Self>(*self, ::core::default::Default::default()).encode_as_field(tag, buf)
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                MappedInt::<Self>(*self, ::core::default::Default::default()).encoded_len_as_field(tag)
            }
        }

        #[allow(clippy::all)]
        impl $crate::ProtoEncodeRepeated for $t {
            fn encode_as_field_repeated<'a, I>(
                iter: I,
                tag: ::core::num::NonZeroU32,
                buf: &mut dyn $crate::bytes::BufMut,
            )
            where
                I: ExactSizeIterator<Item = &'a Self> + Clone,
                Self: 'a,
            {
                MappedInt::<Self>::encode_as_field_repeated(
                    iter,
                    tag,
                    buf,
                );
            }

            fn encoded_len_as_field_repeated<'a, I>(iter: I, tag: ::core::num::NonZeroU32) -> usize
            where
                I: ExactSizeIterator<Item = &'a Self>,
                Self: 'a,
            {
                MappedInt::<Self>::encoded_len_as_field_repeated(
                    iter,
                    tag,
                )
            }
        }

        #[allow(clippy::all)]
        impl $crate::ProtoMergeRepeated for $t {
            fn merge_repeated<T>(
                values: &mut T,
                wire_type: WireType,
                buf: &mut dyn bytes::Buf,
                ctx: DecodeContext,
            ) -> Result<(), prost::DecodeError>
            where
                T: std::iter::Extend<Self>,
            {
                <MappedInt::<Self> as $crate::ProtoMergeRepeated>::merge_repeated(
                    &mut $crate::MapExtend::new(values, |MappedInt(i, _)| i),
                    wire_type,
                    buf,
                    ctx,
                )
            }
        }

        #[allow(clippy::all)]
        impl $crate::Proto for $t {
            fn merge_self(
                &mut self,
                wire_type: WireType,
                buf: &mut dyn $crate::prost::bytes::Buf,
                ctx: DecodeContext,
            ) -> Result<(), $crate::prost::DecodeError> {
                let mut mapped = MappedInt::<Self>(*self, ::core::default::Default::default());
                mapped.merge_self(wire_type, buf, ctx)?;

                *self = mapped.0;

                Ok(())
            }
        }

    };
}

/// Because of the orphan rule, we can't just automatically implement this for all
/// types which implement `ProtoStruct`. Therefore, we just add a simple macro that
/// makes it almost as simple as a generic impl.
#[macro_export]
macro_rules! impl_message_for_protostruct {
    (
        impl$(<$($pname:ident),*$(; $(const $cname:ident : $cty:ty),*)?>)? Message for $t:ty
        $(where $($bounded:ty : $bound:path,)* $(where $($lbounded:ty : $lbound:lifetime),*)?)?
    ) => {
        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::prost::Message for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
            where
                __Buffer: $crate::prost::bytes::BufMut,
            {
                for (tag, field) in self.fields() {
                    field.encode_as_field(tag, buf)
                }
            }

            fn merge_field<__Buffer: $crate::prost::bytes::Buf>(
                &mut self,
                tag: u32,
                wire_type: $crate::prost::encoding::WireType,
                buf: &mut __Buffer,
                ctx: $crate::prost::encoding::DecodeContext,
            ) -> Result<(), $crate::prost::DecodeError> {
                if let Some(field) = self.field_mut() {
                    field.merge(wire_type, buf, ctx)?;
                }
            }

            fn encoded_len(&self) -> usize {
                self.fields()
                    .map(|(tag, field)| field.encoded_len_as_field(tag))
                    .sum()
            }

            fn clear(&mut self) {
                *self = <Self as Default>::default();
            }
        }

        $crate::impl_proto_for_message!(
            impl$(<$($pname),*$(; $(const $cname : $cty),*)?>)? Proto for $t
                $(where $($bounded : $bound,)* $(where $($lbounded : $lbound),*)?)?
        );
    };
}

/// Because of the orphan rule, we can't just automatically implement this for all
/// types which implement `ProtoStruct`. Therefore, we just add a simple macro that
/// makes it almost as simple as a generic impl.
#[macro_export]
macro_rules! impl_message_for_protooneof {
    (
        impl$(<$($pname:ident),*$(; $(const $cname:ident : $cty:ty),*)?>)? Proto for $t:ty
        $(where $($bounded:ty : $bound:path,)* $(where $($lbounded:ty : $lbound:lifetime),*)?)?
    ) => {
        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::prost::Message for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
            where
                __Buffer: $crate::prost::bytes::BufMut,
            {
                let (tag, inner) = <Self as $crate::ProtoOneof>::variant(self);

                inner.encode_as_field(tag);
            }

            fn merge_field<__Buffer: $crate::prost::bytes::Buf>(
                &mut self,
                tag: u32,
                wire_type: WireType,
                buf: &mut __Buffer,
                ctx: DecodeContext,
            ) -> Result<(), $crate::prost::DecodeError> {
                self.exec_merge(|field| field.merge(wire_type, buf, ctx))
            }

            fn encoded_len(&self) -> usize {
                self.fields()
                    .map(|(tag, field)| field.encoded_len_as_field(tag))
                    .sum()
            }

            fn clear(&mut self) {
                *self = <Self as Default>::default();
            }
        }
    };
}

#[macro_export]
macro_rules! impl_proto_for_protorepeated {
    (
        impl$(<$($pname:ident),*$(; $(const $cname:ident : $cty:ty),*)?>)? Proto for $t:ty
        $(where $($bounded:ty : $bound:path,)* $(where $($lbounded:ty : $lbound:lifetime),*)?)?
    ) => {
        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::IsDefault for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn is_default(&self) -> bool {
                <
                    <Self as $crate::ProtoRepeated>::Iter<'_>
                        as ::core::iter::ExactSizeIterator
                >::len(&$crate::ProtoRepeated::iter(self)) == 0
            }
        }

        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::ProtoEncode for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, buf: &mut dyn $crate::prost::bytes::BufMut) {
                if !$crate::IsDefault::is_default(self) {
                    <<Self as $crate::ProtoRepeated>::Item as $crate::ProtoEncodeRepeated>::encode_as_field_repeated(
                        <Self as $crate::ProtoRepeated>::iter(self),
                        tag,
                        buf,
                    )
                }
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                if $crate::IsDefault::is_default(self) {
                    0
                } else {
                    <Self as ProtoRepeated>::Item::encoded_len_as_field_repeated(
                        <Self as ProtoRepeated>::iter(self),
                        tag,
                    )
                }
            }
        }

        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::Proto for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn merge_self(
                &mut self,
                wire_type: WireType,
                buf: &mut dyn $crate::prost::bytes::Buf,
                ctx: DecodeContext,
            ) -> Result<(), $crate::prost::DecodeError> {
                <<Self as $crate::ProtoRepeated>::Item as $crate::ProtoMergeRepeated>::merge_repeated(
                    self,
                    wire_type,
                    buf,
                    ctx,
                )
            }
        }
    };
}

#[macro_export]
macro_rules! impl_proto_for_protomap {
    (
        impl$(<$($pname:ident),*$(; $(const $cname:ident : $cty:ty),*)?>)? Proto for $t:ty
        $(where $($bounded:ty : $bound:path,)* $(where $($lbounded:ty : $lbound:lifetime),*)?)?
    ) => {
        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::IsDefault for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn is_default(&self) -> bool {
                $crate::ProtoMap::iter(self).size_hint().1 == Some(0)
            }
        }

        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::ProtoEncode for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn encode_as_field(
                &self,
                tag: ::core::num::NonZeroU32,
                mut buf: &mut dyn $crate::prost::bytes::BufMut
            ) {
                use ::core::num::NonZeroU32;

                for (key, val) in <Self as $crate::ProtoMap>::iter(self) {
                    let len = {
                        let key_len =
                            $crate::ProtoEncode::encoded_len_as_field(key, NonZeroU32::new(1).unwrap());

                        let val_len =
                            $crate::ProtoEncode::encoded_len_as_field(val, NonZeroU32::new(2).unwrap());

                        key_len + val_len
                    };

                    $crate::prost::encoding::encode_key(tag.get(), WireType::LengthDelimited, &mut buf);
                    $crate::prost::encoding::encode_varint(len as u64, &mut buf);
                    $crate::ProtoEncode::encode_as_field(key, NonZeroU32::new(1).unwrap(), buf);
                    $crate::ProtoEncode::encode_as_field(val, NonZeroU32::new(2).unwrap(), buf);
                }
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                use ::core::num::NonZeroU32;

                <Self as $crate::ProtoMap>::iter(self)
                    .map(|(key, val)| {
                        let len = (
                            $crate::ProtoEncode::encoded_len_as_field(key, NonZeroU32::new(1).unwrap())
                                + $crate::ProtoEncode::encoded_len_as_field(val, NonZeroU32::new(2).unwrap())
                        );
                        $crate::prost::encoding::key_len(tag.get()) + $crate::prost::encoding::encoded_len_varint(len as u64) + len
                    })
                    .sum::<usize>()
            }
        }

        impl$(<$($pname,)* $($(const $cname : $cty),*)?>)? $crate::Proto for $t
        $(where $($bounded : $bound,)* $($($lbounded : $lbound),*)?)?
        {
            fn merge_self(
                &mut self,
                _wire_type: $crate::prost::encoding::WireType,
                mut buf: &mut dyn $crate::prost::bytes::Buf,
                ctx: $crate::prost::encoding::DecodeContext,
            ) -> Result<(), $crate::prost::DecodeError> {
                let mut key = Default::default();
                let mut val = Default::default();

                $crate::prost::encoding::merge_loop(
                    &mut (&mut key, &mut val),
                    &mut buf,
                    ctx,
                    |(key, val), buf, ctx| {
                        let (tag, wire_type) = $crate::prost::encoding::decode_key(buf)?;
                        match tag {
                            1 => <
                                <Self as $crate::ProtoMap>::Key as $crate::Proto
                            >::merge_self(key, wire_type, buf, ctx),
                            2 => <
                                <Self as $crate::ProtoMap>::Value as $crate::Proto
                            >::merge_self(val, wire_type, buf, ctx),
                            _ => $crate::prost::encoding::skip_field(wire_type, tag, buf, ctx),
                        }
                    },
                )?;

                <Self as $crate::ProtoMap>::insert(self, key, val);

                Ok(())
            }
        }
    };
}
