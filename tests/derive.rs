#![feature(generic_associated_types)]

#[derive(Default, Debug, autoproto::Message)]
struct Unit;

#[derive(Default, Debug, autoproto::Message)]
struct Foo<A, B>(#[autoproto(tag = 4)] A, #[autoproto(tag = 5)] B);

#[derive(Default, Debug, autoproto::Message)]
struct SomeStruct<A, B> {
    a: A,
    b: B,
}

#[derive(Default, Debug, autoproto::Message)]
#[autoproto(transparent)]
struct Wrapper(SomeStruct<Foo<u32, u64>, SomeStruct<f32, Unit>>);

#[derive(Debug, autoproto::Message)]
enum Oneof<A, B, C> {
    Nothing,
    First { a: A, b: B },
    Second(C),
}

impl<A, B, C> Default for Oneof<A, B, C> {
    fn default() -> Self {
        Self::Nothing
    }
}

impl<A, B, C> autoproto::IsDefault for Oneof<A, B, C> {
    fn is_default(&self) -> bool {
        match self {
            Nothing => true,
            _ => false,
        }
    }
}
