# Autoproto

This crate implements a custom derive macro for the `prost::Message` trait, along with including
some helper traits to make automatic derivation as simple as possible - basically putting more
information in the type system instead of in the macro implementation. If the macro doesn't do
something that you need it to do, you can implement one of the "base traits" like `ProtoStruct` and
`ProtoOneof` and use the functions in the `generic` module to implement the rest of the traits.

### Limitations

#### (Currently) no oneof-nested-within-struct

This can be lifted eventually, but right now a major limitation of this derive macro is that we
cannot support protobuf types like so:

```proto
message Foo {
    string first = 1;
    oneof some_oneof {
        string second = 2;
        string third = 3;
    }
}
```

As the library is written, it will only support `oneof` when it is the only member of a message.

#### No automatic generation from `.proto` files

This is the biggest change from `prost`, and was a deliberate choice. I consider automatically
generating the Rust files from protobuf files to be (at least in part) a misfeature of `prost`,
since for many cases it leads to extremely unwieldy types in Rust. Rust has a deep and rich type
system and it isn't possible for Protobuf to nicely represent it. Eventually I want to have compile-
time checking that a Rust type is compatible with a given protobuf file, but this is currently not
implemented.

### Improvements and changes from `#[derive(prost::Message)]`

#### Supporting more types as fields

This macro supports collections other than `Vec` for repeated fields, bare enumerations in structs,
`usize`/`isize`, and maps. For repeated collections, any type that implements `std::iter::Extend`
and where a reference to that type can be iterated over can be used as a collection in a struct.
Currently you must manually implement `Proto` and `ProtoEncode` for these types, but if and when
`feature(specialization)` is stablised this restriction should hopefully be lifted.

While currently we cannot automatically support any type implementing `proto::Message` as a field -
because that trait is implemented for scalars and the main reason we have our own trait is so we can
have a different impl for scalars - you just need to implement the `IsMessage` marker trait to allow
the type to be used as a field in a `#[derive(autoproto::Message)]` type.

Also, messages no longer need to be wrapped in an `Option`, as protobuf's eager decoding already
requires that all messages implement `Default`. You can wrap any type in an `Option` if you want to
distinguish between a field being supplied with default values or not supplied at all.

#### Deriving for more kinds of types

This macro allows deriving for pretty much any tagged union, and deriving for generic structures.
For example:

```rust,no_run
# #![feature(generic_associated_types)]
#[derive(Copy, Clone, PartialEq, Debug, autoproto::Message)]
enum Oneof<A, B, C> {
    Nothing,
    One(A),
    Two(A, B),
    Three(A, B, C),
}
```

#### No mixed tagged-untagged structs

One change from the `prost` macro is that either all fields must be tagged or no fields can be
tagged. For example, these two are ok:

```rust
# #![feature(generic_associated_types)]
#[derive(Copy, Clone, PartialEq, Default, Debug, autoproto::Message)]
struct SomeStructTagged<A, B, C, D, E> {
    #[autoproto(tag = 1)]
    a: A,
    #[autoproto(tag = 2)]
    b: B,
    #[autoproto(tag = 3)]
    c: C,
    #[autoproto(tag = 4)]
    d: D,
    #[autoproto(tag = 5)]
    e: E,
}
#[derive(Copy, Clone, PartialEq, Default, Debug, autoproto::Message)]
struct SomeStruct<A, B, C, D, E> {
    a: A,
    b: B,
    c: C,
    d: D,
    e: E,
}
```

But the following is not:

```rust,compile_fail
# #![feature(generic_associated_types)]
#[derive(Copy, Clone, PartialEq, Default, Debug, autoproto::Message)]
struct SomeStruct<A, B, C, D, E> {
    a: A,
    b: B,
    #[autoproto(tag = 1)]
    c: C,
    d: D,
    e: E,
}
```
