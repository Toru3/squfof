#Shanks's square forms factorization

## example
```rust
use squfof::square_form_factorization;
let n = 991 * 997;
let f = square_form_factorization(n).unwrap();
assert!(f == 991 || f == 997);
```
