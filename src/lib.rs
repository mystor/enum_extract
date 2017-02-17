//! This crate provides 2 macros, `extract!` and `let_extract!`. See their
//! individual macro-level documentation for more information.

/// Extract the fields of a single variant from an enum, returning an
/// `Option<T>` where `T` is either the single field, or a tuple of each of the
/// fields in the order they are written.
///
/// ## Examples
///
/// Given the following enum:
///
/// ```ignore
/// enum Foo {
///     A(i32),
///     B(i32, i32),
///     C { x: i32, y: i32 },
///     D { z: i32 },
/// }
/// ```
///
/// If the variant matches, it produces a `Some` of the fields in the matched
/// variant.
///
/// ```rust
/// # #[macro_use] extern crate enum_extract;
/// # enum Foo {
/// #     A(i32),
/// #     B(i32, i32),
/// #     C { x: i32, y: i32 },
/// #     D { z: i32 },
/// # }
/// # fn main() {
/// let a = Foo::A(10);
/// assert_eq!(extract!(Foo::A(_), a), Some(10));
///
/// let d = Foo::D{ z: 20 };
/// assert_eq!(extract!(Foo::D{z}, d), Some(20));
/// # }
/// ```
///
/// If there is more than one field in the enum variant, it produces a `Some` of a tuple
///
/// ```rust
/// # #[macro_use] extern crate enum_extract;
/// # enum Foo {
/// #     A(i32),
/// #     B(i32, i32),
/// #     C { x: i32, y: i32 },
/// #     D { z: i32 },
/// # }
/// # fn main() {
/// let b = Foo::B(10, 20);
/// assert_eq!(extract!(Foo::B(_, _), b), Some((10, 20)));
///
/// let c = Foo::C{ x: 30, y: 40 };
/// assert_eq!(extract!(Foo::C{x, y}, c), Some((30, 40)));
///
/// // You can also control the order of the fields in the struct variant case!
/// assert_eq!(extract!(Foo::C{y, x}, c), Some((40, 30)));
/// # }
/// ```
///
/// If the pattern doesn't match, it produces a `None`
///
/// ```rust
/// # #[macro_use] extern crate enum_extract;
/// # enum Foo {
/// #     A(i32),
/// #     B(i32, i32),
/// #     C { x: i32, y: i32 },
/// #     D { z: i32 },
/// # }
/// # fn main() {
/// let b = Foo::B(10, 20);
/// assert_eq!(extract!(Foo::A(_), b), None);
/// # }
/// ```
#[macro_export]
macro_rules! extract {
    // Internal Variants
    (@ANON_TUPLE [], [$($ids:ident)*], $($p:ident)::+, $t:expr) => {
        match $t {
            $($p)::+ ( $($ids),* ) => Some(( $($ids),* )),
            _ => None,
        }
    };
    (@ANON_TUPLE [_], [$($ids:ident)*], $($p:ident)::+, $t:expr) => {
        extract!(@ANON_TUPLE
                 [],
                 [$($ids)* x],
                 $($p)::+,
                 $t)
    };
    (@ANON_TUPLE [_, $($more:tt)*], [$($ids:ident)*], $($p:ident)::+, $t:expr) => {
        extract!(@ANON_TUPLE
                 [$($more)*],
                 [$($ids)* x],
                 $($p)::+,
                 $t)
    };

    // Struct Variants
    ($($p:ident)::+ { $($i:ident),* } , $t:expr) => {
        match $t {
            $($p)::+ {$($i),*} => Some(($($i),*)),
            _ => None
        }
    };

    // Tuple Variants
    ($($p:ident)::+ ( $($its:tt)* ) , $t:expr) => {
        extract!(@ANON_TUPLE
                 [$($its)*],
                 [],
                 $($p)::+,
                 $t)
    };
}

/// Extract the fields of a single variant from an enum, binding them into the
/// current scope.
///
/// If the binding fails due to the variant being incorrect, execute the error
/// expression. Alternatively, a partial `match` block may be written to handle
/// the remaining cases.
///
/// ## Examples
///
/// Given the following enum:
///
/// ```ignore
/// enum Foo {
///     A(i32),
///     B(i32, i32),
///     C { x: i32, y: i32 },
///     D { z: i32 },
/// }
/// ```
///
/// If the extract succeeds, the variable names written bind into the current
/// scope.
///
/// ```rust
/// # #[macro_use] extern crate enum_extract;
/// # enum Foo {
/// #     A(i32),
/// #     B(i32, i32),
/// #     C { x: i32, y: i32 },
/// #     D { z: i32 },
/// # }
/// # fn main() {
/// let a = Foo::A(10);
/// let_extract!(Foo::A(x), a, panic!());
/// assert_eq!(x, 10);
/// # }
/// ```
///
/// If it fails, the expression passed in as the 3rd argument is executed
/// instead, and can cause execution to diverge.
///
/// ```rust
/// # #[macro_use] extern crate enum_extract;
/// # enum Foo {
/// #     A(i32),
/// #     B(i32, i32),
/// #     C { x: i32, y: i32 },
/// #     D { z: i32 },
/// # }
/// # fn main() {
/// let a = Foo::A(10);
/// let_extract!(Foo::B(x, y), a, return);
/// unreachable!();
/// # }
/// ```
///
/// Alternatively, it can provide default values for the variable bindings, from
/// left to right.
///
/// ```rust
/// # #[macro_use] extern crate enum_extract;
/// # enum Foo {
/// #     A(i32),
/// #     B(i32, i32),
/// #     C { x: i32, y: i32 },
/// #     D { z: i32 },
/// # }
/// # fn main() {
/// let a = Foo::A(10);
/// let_extract!(Foo::B(x, y), a, (40, 50));
/// assert_eq!(x, 40);
/// assert_eq!(y, 50);
/// # }
/// ```
///
/// The other cases can each be handled specifically with a match-like block.
///
/// ```rust
/// # #[macro_use] extern crate enum_extract;
/// # enum Foo {
/// #     A(i32),
/// #     B(i32, i32),
/// #     C { x: i32, y: i32 },
/// #     D { z: i32 },
/// # }
/// # fn main() {
/// let a = Foo::A(10);
/// let_extract!(Foo::B(x, y), a, match {
///     Foo::A(x) => return,
///     Foo::C{..} => unreachable!(),
///     Foo::D{..} => unreachable!(),
/// });
/// unreachable!();
/// # }
/// ```
///
/// Struct variants are also supported, and can be written either as `{ field }`
/// or `{ field: binding }`.
///
/// ```rust
/// # #[macro_use] extern crate enum_extract;
/// # enum Foo {
/// #     A(i32),
/// #     B(i32, i32),
/// #     C { x: i32, y: i32 },
/// #     D { z: i32 },
/// # }
/// # fn main() {
/// let d = Foo::D { z: 10 };
/// let_extract!(Foo::D{ z }, d, unreachable!());
/// assert_eq!(z, 10);
///
/// let_extract!(Foo::D{ z: apples }, d, unreachable!());
/// assert_eq!(apples, 10);
/// # }
/// ```
#[macro_export]
macro_rules! let_extract {
    ($($p:ident)::+ ( $($i:ident),* ) , $t:expr, match { $($body:tt)* }) => {
        let ($($i,)*) = match $t {
            $($p)::+ ($($i),*) => ($($i,)*),
            $($body)*
        };
    };
    ($($p:ident)::+ { $($i:ident),* } , $t:expr, match { $($body:tt)* }) => {
        let ($($i,)*) = match $t {
            $($p)::+ {$($i),*} => ($($i,)*),
            $($body)*
        };
    };
    ($($p:ident)::+ { $($k:ident : $v:ident),* } , $t:expr, match { $($body:tt)* }) => {
        let ($($v,)*) = match $t {
            $($p)::+ {$($k),*} => ($($k,)*),
            $($body)*
        };
    };

    ($($p:ident)::+ ( $($its:tt)* ) , $t:expr, $els:expr) => {
        let_extract!($($p)::+ ( $($its)* ) , $t, match { _ => $els })
    };
    ($($p:ident)::+ { $($its:tt)* } , $t:expr, $els:expr) => {
        let_extract!($($p)::+ { $($its)* } , $t, match { _ => $els })
    };

}

#[cfg(test)]
mod test {
    enum Foo {
        A(u32, u32),
        B(u32)
    }

    enum Bar {
        C { x: u32, y: u32 },
        D { z: u32 },
    }

    #[test]
    fn test() {
        let f: Foo = Foo::A(10, 20);

        let x = extract!(Foo::A(_, _), f);
        assert_eq!(x, Some((10, 20)));

        let_extract!(Foo::A(x, y), f, panic!());
        assert_eq!(x, 10);
        assert_eq!(y, 20);

        let f: Foo = Foo::B(8);
        let x = extract!(Foo::B(_), f);
        assert_eq!(x, Some(8));

        let_extract!(Foo::B(z), f, panic!());
        assert_eq!(z, 8);

        let f: Bar = Bar::C{ x: 10, y: 20 };

        let x = extract!(Bar::C{x, y}, f);
        assert_eq!(x, Some((10, 20)));

        let_extract!(Bar::C{x, y}, f, panic!());
        assert_eq!(x, 10);
        assert_eq!(y, 20);

        let_extract!(Bar::C{x: a, y: b}, f, panic!());
        assert_eq!(a, 10);
        assert_eq!(b, 20);

        let f: Bar = Bar::D{ z: 8 };
        let x = extract!(Bar::D{z}, f);
        assert_eq!(x, Some(8));

        let_extract!(Bar::D{z}, f, panic!());
        assert_eq!(z, 8);

        let_extract!(Bar::D{z: x}, f, panic!());
        assert_eq!(x, 8);

        // let f: Bar = Bar::C{ x: 10, y: 20 };
        let_extract!(Bar::D{z}, f, match {
            Bar::C{x, y} => panic!("Saw {:?} {:?}", x, y)
        });
        assert_eq!(z, 8);
    }

    #[test]
    fn alternate_result() {
        let f: Foo = Foo::A(10, 20);

        let_extract!(Foo::B(x), f, match { Foo::A(x, _) => (x,) });
        assert_eq!(x, 10);

        let_extract!(Some(y), None, (10,));
        assert_eq!(y, 10);
    }
}
