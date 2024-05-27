#![doc = include_str!("../README.md")]

use std::{
    borrow::Cow,
    collections::{
        BTreeMap,
        BTreeSet,
        BinaryHeap,
        HashMap,
        HashSet,
        LinkedList,
        VecDeque,
    },
    convert::Infallible,
    rc::Rc,
    sync::Arc,
    task::Poll,
    iter::FusedIterator,
};

/// Similar to the automatic implicit conversion to boolean values
/// in weakly typed languages
///
/// | type                          | impl                  |
/// | ---                           | ---                   |
/// | float                         | self is not 0.0 / NaN |
/// | integer                       | self != 0             |
/// | reference / smart pointer     | inner value impl      |
/// | raw pointer                   | !self.is_null         |
/// | Option                        | self.is_some          |
/// | Result                        | self.is_ok            |
/// | Poll                          | self.is_ready         |
/// | str / slice                   | self.is_empty         |
/// | collections                   | self.is_empty         |
/// | unit                          | false                 |
/// | bool                          | self                  |
/// | fn / tuple                    | true                  |
pub trait WeakTrue {
    /// Similar to the automatic implicit conversion to boolean values
    /// in weakly typed languages
    ///
    /// # Examples
    /// ```
    /// # use weak_true::WeakTrue;
    ///
    /// assert!("c".weak_true());
    /// assert!('c'.weak_true());
    /// assert!('\0'.weak_true());
    /// assert!([0].weak_true());
    /// assert!((&0 as *const i32).weak_true());
    /// assert!(Some(0).weak_true());
    ///
    /// assert!(f64::NAN.weak_false());
    /// assert!(0.0.weak_false());
    /// assert!(0.weak_false());
    /// assert!("".weak_false());
    /// assert!([0; 0].weak_false());
    /// ```
    ///
    /// Refer to the documentation on [`WeakTrue`]
    ///
    /// [`WeakTrue`]: crate::WeakTrue
    fn weak_true(&self) -> bool;

    /// Default implementation is [`weak_true`] inversion
    ///
    /// [`weak_true`]: crate::WeakTrue::weak_true
    fn weak_false(&self) -> bool {
        !self.weak_true()
    }
}

fn weak_bool<const B: bool>(value: impl WeakTrue) -> bool {
    if B {
        value.weak_true()
    } else {
        value.weak_false()
    }
}
pub trait WeakBoolIterExtend: Sized {
    /// like `iter.map(WeakTrue::weak_true)`
    fn weak_true(self) -> WeakBoolIter<true, Self>;

    /// like `iter.map(WeakTrue::weak_false)`
    fn weak_false(self) -> WeakBoolIter<false, Self>;
}
impl<I> WeakBoolIterExtend for I
where I: Iterator,
      I::Item: WeakTrue,
{
    fn weak_true(self) -> WeakBoolIter<true, Self> {
        WeakBoolIter(self)
    }

    fn weak_false(self) -> WeakBoolIter<false, Self> {
        WeakBoolIter(self)
    }
}

/// Created from [`weak_true`] and [`weak_false`] method
///
/// [`weak_true`]: crate::WeakBoolIterExtend::weak_true
/// [`weak_false`]: crate::WeakBoolIterExtend::weak_false
pub struct WeakBoolIter<const B: bool, I>(I);

impl<const B: bool, I> ExactSizeIterator for WeakBoolIter<B, I>
where I::Item: WeakTrue,
      I: ExactSizeIterator,
{ }
impl<const B: bool, I> FusedIterator for WeakBoolIter<B, I>
where I::Item: WeakTrue,
      I: FusedIterator,
{ }
impl<const B: bool, I> Iterator for WeakBoolIter<B, I>
where I: Iterator,
      I::Item: WeakTrue,
{
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(weak_bool::<B>)
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth(n).map(weak_bool::<B>)
    }

    fn fold<B1, F>(self, init: B1, mut f: F) -> B1
    where Self: Sized,
          F: FnMut(B1, Self::Item) -> B1,
    {
        self.0.fold(init, |acc, elem| f(acc, weak_bool::<B>(elem)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
impl<const B: bool, I> DoubleEndedIterator for WeakBoolIter<B, I>
where I: DoubleEndedIterator,
      I::Item: WeakTrue,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(weak_bool::<B>)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth_back(n).map(weak_bool::<B>)
    }

    fn rfold<B1, F>(self, init: B1, mut f: F) -> B1
    where
        Self: Sized,
        F: FnMut(B1, Self::Item) -> B1,
    {
        self.0.rfold(init, |acc, elem| f(acc, weak_bool::<B>(elem)))
    }
}

#[doc = "\
if but use [`weak_true`] result value

# Examples
```
# use weak_true::wif;
let r = wif!(\"\" => {
    1
} else {
    0
});
assert_eq!(r, 0);

wif!(\"\" => {
    unreachable!()
});
wif!('\\0' => { } else {
    unreachable!()
});
```

[`weak_true`]: crate::WeakTrue::weak_true
"]
#[macro_export]
macro_rules! wif {
    ($cond:expr => $true:block $(else $false:block)?) => {
        if $crate::WeakTrue::weak_true(&$cond)
        $true $(else $false)?
    };
}

macro_rules! impls {
    ($self:ident {
        $(
            $cond:expr =>
            $($ty:ty $(=> [$($g:tt)*])?),+ $(,)?;
        )*
    }) => {
        $(
            impls!(@impl($self) $cond => $($ty $(=> [$($g)*])?),+);
        )*
    };
    (
        @impl($self:ident)
        $cond:expr =>
        $($ty:ty $(=> [$($g:tt)*])?),+
    ) => {
        $(
            impl$(<$($g)*>)? WeakTrue for $ty {
                fn weak_true(&$self) -> bool {
                    $cond
                }
            }
        )+
    };
}

impls!(self {
    unreachable!()  => Infallible;
    false           => ();
    *self           => bool;
    true            => char;
    *self != 0      => u8, u16, u32, u64, u128, usize,
                       i8, i16, i32, i64, i128, isize;
    *self != 0.0 && !self.is_nan() => f32, f64;
    !self.is_empty() =>
        str,
        String,
        [T]                 => [T],
        [T; N]              => [T, const N: usize],
        Vec<T>              => [T],
        VecDeque<T>         => [T],
        LinkedList<T>       => [T],
        HashMap<K, V, H>    => [K, V, H],
        HashSet<T, H>       => [T, H],
        BTreeMap<K, V>      => [K, V],
        BTreeSet<T>         => [T],
        BinaryHeap<K>       => [K],
        ;
    <T as WeakTrue>::weak_true(&**self) =>
        &'_ T       => [T: WeakTrue + ?Sized],
        &'_ mut T   => [T: WeakTrue + ?Sized],
        Box<T>      => [T: WeakTrue + ?Sized],
        Rc<T>       => [T: WeakTrue + ?Sized],
        Arc<T>      => [T: WeakTrue + ?Sized],
        Cow<'_, T>  => [T: WeakTrue + ?Sized + ToOwned],
        ;
    !self.is_null() =>
        *const T    => [T: ?Sized],
        *mut T      => [T: ?Sized],
        ;
    self.is_some()  => Option<T> => [T];
    self.is_ok()    => Result<T, E> => [T, E];
    self.is_ready() => Poll<T> => [T];
});

macro_rules! impl_tuples {
    ($f:ident $($g:ident)*) => {
        impl_tuples!($($g)*);
        #[doc(hidden)]
        impl<$f, $($g),*> WeakTrue for ($f, $($g),*) {
            fn weak_true(&self) -> bool {
                true
            }
        }
        #[doc(hidden)]
        impl<$f, R, $($g),*> WeakTrue for fn($f, $($g),*) -> R {
            fn weak_true(&self) -> bool {
                true
            }
        }
    };
    () => ();
}

impl_tuples!(T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16);
impl<R> WeakTrue for fn() -> R {
    fn weak_true(&self) -> bool {
        true
    }
}

#[cfg(test)]
mod tests {
    use core::fmt::Debug;
    use std::{ptr::{null, null_mut}, collections::HashSet};
    use crate::WeakBoolIterExtend;

    use super::WeakTrue;

    trait TestTrait: WeakTrue + Debug { }
    impl<T: WeakTrue + Debug> TestTrait for T { }

    macro_rules! run_data {
        ($($e:expr),+ $(,)?) => {{
            [$({
                let __value: Box<dyn TestTrait>
                    = Box::new($e);
                __value
            }),+]
        }};
    }

    #[test]
    fn test() {
        let datas = run_data![
            true,
            1i32,
            10u8,
            &2,
            "a",
            &"a",
            "ab",
            '\0',
            'c',
            ['c'],
            &['c'],
            &['c'][..],
            [0],
            vec![0],
            true,
            (0,),
            (0, 0),
            (|| ()) as fn(),
            (|| 0) as fn() -> i32,
            (|_| ()) as fn(i32),
            (|_| 0) as fn(i32) -> i32,
            &0 as *const i32,
            Some(0),
            Ok::<_, ()>(0),
            Some(1),
            Ok::<_, ()>(1),
        ];
        for data in datas.iter().weak_true() {
            assert!(data.weak_true(),   "{data:?}");
            assert!(!data.weak_false(), "{data:?}");
        }
        for data in datas.iter().weak_false() {
            assert!(! data.weak_true(),   "{data:?}");
            assert!(! !data.weak_false(), "{data:?}");
        }
        for data in datas {
            assert!(data.weak_true(),   "{data:?}");
            assert!(!data.weak_false(), "{data:?}");
        }
    }

    #[test]
    fn test_false() {
        let datas = run_data![
            false,
            0,
            0.0,
            0.0f32,
            f32::NAN,
            f64::NAN,
            &0,
            &0.0,
            &0.0f32,
            &f32::NAN,
            &f64::NAN,
            [0; 0],
            &[0; 0][..],
            null::<i32>(),
            null_mut::<i32>(),
            vec![0; 0],
            Vec::<i32>::new(),
            HashSet::<i32>::new(),
            None::<i32>,
            Err::<(), _>(0),
            Err::<(), _>(1),
            (),
        ];
        for data in datas.iter().weak_true() {
            assert!(data.weak_false(),  "{data:?}");
            assert!(!data.weak_true(),  "{data:?}");
        }
        for data in datas.iter().weak_false() {
            assert!(! data.weak_false(),  "{data:?}");
            assert!(! !data.weak_true(),  "{data:?}");
        }
        for data in datas {
            assert!(data.weak_false(),  "{data:?}");
            assert!(!data.weak_true(),  "{data:?}");
        }
    }
}
