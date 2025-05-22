Similar to the automatic implicit conversion to boolean values
in weakly typed languages

| type                          | impl                  |
| ---                           | ---                   |
| float                         | self is not 0.0 / NaN |
| integer                       | self != 0             |
| reference / smart pointer     | inner value impl      |
| raw pointer                   | !self.is\_null        |
| Option                        | self.is\_some         |
| Result                        | self.is\_ok           |
| Poll                          | self.is\_ready        |
| str / slice / array           | !self.is\_empty       |
| collections                   | !self.is\_empty       |
| unit                          | false                 |
| bool                          | self                  |
| fn / tuple / char             | true                  |

# Examples
```rust
use weak_true::weak_true;

#[weak_true]
fn main() {
    let mut a = vec![-1, 0, 1, 2];
    let mut b = vec![4, 3];

    while a && a[a.len()-1] {
        b.push(a.pop().unwrap());
    }

    assert_eq!(a, vec![-1, 0]);
    assert_eq!(b, vec![4, 3, 2, 1]);
}
```

```rust
use weak_true::WeakTrue;

assert!("c".weak_true());
assert!('c'.weak_true());
assert!('\0'.weak_true());
assert!([0].weak_true());
assert!((&0 as *const i32).weak_true());
assert!(Some(0).weak_true());

assert!(f64::NAN.weak_false());
assert!(0.0.weak_false());
assert!(0.weak_false());
assert!("".weak_false());
assert!([0; 0].weak_false());

assert_eq!(1.weak_then(|| "ok"), Some("ok"));
assert_eq!(0.weak_then(|| "ok"), None);
```
