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
```
