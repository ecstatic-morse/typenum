//! This crate provides type-level numbers evaluated at compile time. It depends only on libcore.
//!
//! The traits defined or used in this crate are used in a typical manner. They can be divided into
//! two categories: **marker traits** and **type operators**.
//!
//! Many of the marker traits have functions defined, but they all do essentially the same thing:
//! convert a type into its runtime counterpart, and are really just there for debugging. For
//! example,
//!
//! ```rust
//! use typenum::{N4, Integer};
//!
//! assert_eq!(N4::to_i32(), -4);
//! ```
//!
//! **Type operators** are traits that behave as functions at the type level. These are the meat of
//! this library. Where possible, traits defined in libcore have been used, but their attached
//! functions have not been implemented.
//!
//! For example, the `Add` trait is implemented for both unsigned and signed integers, but the
//! `add` function is not. As there are never any objects of the types defined here, it wouldn't
//! make sense to implement it. What is important is its associated type `Output`, which is where
//! the addition happens.
//!
//! ```rust
//! use std::ops::Add;
//! use typenum::{Integer, P3, P4};
//!
//! type X = <P3 as Add<P4>>::Output;
//! assert_eq!(<X as Integer>::to_i32(), 7);
//! ```
//!
//! In addition, helper aliases are defined for type operators. For example, the above snippet
//! could be replaced with
//!
//! ```rust
//! use typenum::{Sum, Integer, P3, P4};
//!
//! type X = Sum<P3, P4>;
//! assert_eq!(<X as Integer>::to_i32(), 7);
//! ```
//!
//! Documented in each module is the full list of type operators implemented.
//!

#![no_std]
#![warn(missing_docs)]
#![cfg_attr(feature = "i128", recursion_limit = "130")]
#![cfg_attr(not(feature = "i128"), recursion_limit = "66")]
#![cfg_attr(feature = "strict", deny(missing_docs))]
#![cfg_attr(feature = "strict", deny(warnings))]
#![cfg_attr(feature = "cargo-clippy", deny(clippy))]
#![cfg_attr(
    feature = "cargo-clippy",
    allow(type_complexity, len_without_is_empty, new_without_default_derive)
)]

// For debugging macros:
// #![feature(trace_macros)]
// trace_macros!(true);

use core::cmp::Ordering;

include!(concat!(env!("OUT_DIR"), "/consts.rs"));
include!(concat!(env!("OUT_DIR"), "/op.rs"));
pub mod bit;
pub mod int;
pub mod marker_traits;
pub mod operator_aliases;
pub mod private;
pub mod type_operators;
pub mod uint;

pub mod array;

pub use consts::*;
pub use marker_traits::*;
pub use operator_aliases::*;
pub use type_operators::*;

pub use array::{ATerm, TArr};
pub use int::{NInt, PInt};
pub use uint::{UInt, UTerm};

/// A potential output from `Cmp`, this is the type equivalent to the enum variant
/// `core::cmp::Ordering::Greater`.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Copy, Hash, Debug, Default)]
pub struct Greater;

/// A potential output from `Cmp`, this is the type equivalent to the enum variant
/// `core::cmp::Ordering::Less`.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Copy, Hash, Debug, Default)]
pub struct Less;

/// A potential output from `Cmp`, this is the type equivalent to the enum variant
/// `core::cmp::Ordering::Equal`.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Copy, Hash, Debug, Default)]
pub struct Equal;

/// Returns `core::cmp::Ordering::Greater`
impl Ord for Greater {
    #[inline]
    fn to_ordering() -> Ordering {
        Ordering::Greater
    }
}

/// Returns `core::cmp::Ordering::Less`
impl Ord for Less {
    #[inline]
    fn to_ordering() -> Ordering {
        Ordering::Less
    }
}

/// Returns `core::cmp::Ordering::Equal`
impl Ord for Equal {
    #[inline]
    fn to_ordering() -> Ordering {
        Ordering::Equal
    }
}

/// Asserts that two types are the same.
#[macro_export]
macro_rules! assert_type_eq {
    ($a:ty, $b:ty) => {
        let _: <$a as $crate::Same<$b>>::Output;
    };
}

/// Asserts that a type is `True`, aka `B1`.
#[macro_export]
macro_rules! assert_type {
    ($a:ty) => {
        let _: <$a as $crate::Same<True>>::Output;
    };
}

/// Implement `From/Into` to allow conversion between compile-time and runtime integers.
/// Sometimes we must implement `Into` directly to avoid coherence issues.
mod impl_from {
    use consts::*;
    use ::{Unsigned, NonZero, UTerm, UInt, Bit, Integer, PInt, NInt};
    use type_operators::*;
    use operator_aliases::*;

    #[test]
    fn into_u16() {
        type U16Max = Sub1<U65536>;
        let p: u16 = U16Max::new().into();
        let u: u16 = PInt::<U16Max>::new().into();

        assert_eq!(p, ::core::u16::MAX);
        assert_eq!(u, ::core::u16::MAX);
    }

    #[test]
    fn into_i16() {
        type I16Max = Sub1<U32768>;
        let u: i16 = I16Max::new().into();
        let p: i16 = PInt::<I16Max>::new().into();
        let n: i16 = N32768::new().into();

        assert_eq!(u, ::core::i16::MAX);
        assert_eq!(p, ::core::i16::MAX);
        assert_eq!(n, ::core::i16::MIN);
    }

    macro_rules! impl_from {
        (
            $(
                $(#[$meta:meta])*
                $S:ident :: $sfn:ident (), $U:ident :: $ufn:ident () => $bits:ty
             );* $(;)*
        ) => {
            $(
                // UInt

                $(#[$meta])*
                impl From<UTerm> for $U {
                    fn from(_: UTerm) -> $U {
                        0
                    }
                }

                $(#[$meta])*
                impl From<UTerm> for $S {
                    fn from(_: UTerm) -> $S {
                        0
                    }
                }

                $(#[$meta])*
                impl<U, B> Into<$U> for UInt<U, B>
                    where U: Unsigned,
                          B: Bit,
                          UInt<U, B>: IsLess<Shleft<U1, $bits>, Output=True>,
                {
                    fn into(self) -> $U {
                        UInt::<U, B>::$ufn()
                    }
                }

                $(#[$meta])*
                impl<U, B> Into<$S> for UInt<U, B>
                    where U: Unsigned,
                          B: Bit,
                          UInt<U, B>: IsLess<Shleft<U1, Sub1<$bits>>, Output=True>,
                {
                    fn into(self) -> $S {
                        UInt::<U, B>::$sfn()
                    }
                }

                // PInt/NInt

                $(#[$meta])*
                impl From<Z0> for $U {
                    fn from(_: Z0) -> $U {
                        0
                    }
                }

                $(#[$meta])*
                impl From<Z0> for $S {
                    fn from(_: Z0) -> $S {
                        0
                    }
                }

                $(#[$meta])*
                impl<U> Into<$U> for PInt<U>
                    where U: Unsigned +
                             NonZero +
                             IsLess<Shleft<U1, $bits>, Output=True>,
                {
                    fn into(self) -> $U {
                        U::$ufn()
                    }
                }

                $(#[$meta])*
                impl<U> Into<$S> for PInt<U>
                    where U: Unsigned +
                             NonZero +
                             IsLess<Shleft<U1, Sub1<$bits>>, Output=True>,
                {
                    fn into(self) -> $S {
                        PInt::<U>::$sfn()
                    }
                }

                $(#[$meta])*
                impl<U> Into<$S> for NInt<U>
                    where U: Unsigned +
                             NonZero +
                             IsLessOrEqual<Shleft<U1, Sub1<$bits>>, Output=True>,
                {
                    fn into(self) -> $S {
                        NInt::<U>::$sfn()
                    }
                }
             )*
        };
    }

    impl_from! {
        #[cfg(feature = "i128")]
        i128::to_i128(), u128::to_u128() => U128;
        i64::to_i64(),   u64::to_u64()   => U64;
        i32::to_i32(),   u32::to_u32()   => U32;
        i16::to_i16(),   u16::to_u16()   => U16;
        i8::to_i8(),     u8::to_u8()     => U8;

        #[cfg(target_pointer_width = "16")]
        isize::to_isize(), usize::to_usize() => U16;
        #[cfg(target_pointer_width = "32")]
        isize::to_isize(), usize::to_usize() => U32;
        #[cfg(target_pointer_width = "64")]
        isize::to_isize(), usize::to_usize() => U64;
    }
}
