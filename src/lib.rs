#![cfg_attr(not(test), no_std)]
#![feature(step_trait)]
use arrayvec::ArrayVec;
use core::iter::Step;
use num_traits::int::PrimInt;
use ring_algorithm::gcd;

fn bits<T: PrimInt>(n: T) -> u32 {
    let t_bits = T::zero().count_zeros();
    t_bits - n.leading_zeros()
}

fn sqrt<T: PrimInt>(n: T) -> Option<T> {
    if n < T::zero() {
        return None;
    } else if n.is_zero() {
        return Some(T::zero());
    }
    let s = (bits(n) + 1) / 2;
    let mut x = T::one().unsigned_shl(s);
    loop {
        let t = n / x;
        let nx = (x + t).unsigned_shr(1);
        if nx >= x {
            return Some(x);
        }
        x = nx;
    }
}

fn is_parfect_square<T: PrimInt>(n: T) -> bool {
    // seq 128 | sed 's/\(.*\)/\1 * \1 % 128/' | bc | sort -n | uniq | perl -e 'my @c=(); for(0..128){push(@c, 0);} while(<>){chomp; $c[$_]=1;} print(reverse(@c));'
    const MOD128: u128 = 0b000000010000000100000001000010010000000100000001000000010000100110000001000000010000000100001001000000010000000110000001000010011;
    if let Some(div) = T::from(128) {
        if (1u128 << (n % div).to_u32().unwrap()) & MOD128 == 0 {
            return false;
        }
    }
    let sn = sqrt(n).unwrap();
    n == sn * sn
}

fn foward_step<T: PrimInt + Step, const N: usize>(nn: T, k: T, limit: T, sn: T) -> Option<(T, T)>
where
    for<'x> &'x T: core::ops::Rem<&'x T, Output = T>,
{
    let mut q_remain = ArrayVec::<T, N>::new();
    let k2 = k.unsigned_shl(1);
    let up = limit * k2;
    let mut p0 = sn;
    let mut q0 = T::one();
    let mut q1 = nn - sn * sn;
    for _ in T::zero()..limit.unsigned_shl(2) {
        let b = (sn + p0) / q1;
        let p1 = b * q1 - p0;
        let q2 = if p0 >= p1 {
            q0 + b * (p0 - p1)
        } else {
            q0 - b * (p1 - p0)
        };
        p0 = p1;
        q0 = q1;
        q1 = q2;
        if is_parfect_square(q1) {
            let sq = sqrt(q1).unwrap();
            if !q_remain.iter().any(|q| *q == sq) {
                return Some((sq, p0));
            }
        } else if q1 < up {
            let t = q1 / gcd(k2, q1);
            if t < limit {
                if q_remain.len() >= N {
                    return None;
                }
                q_remain.push(t);
            }
        }
    }
    None
}

fn backward_step<T: PrimInt + Step>(mut p0: T, mut q0: T, mut q1: T, limit: T, sn: T) -> Option<T> {
    for _ in T::zero()..limit.unsigned_shl(2) {
        let b = (sn + p0) / q1;
        let p1 = b * q1 - p0;
        let q2 = if p0 >= p1 {
            q0 + b * (p0 - p1)
        } else {
            q0 - b * (p1 - p0)
        };
        if p0 == p1 {
            return Some(q1);
        }
        p0 = p1;
        q0 = q1;
        q1 = q2;
    }
    None
}

fn square_form_factorization_aux<T: PrimInt + Step, const N: usize>(
    n: T,
    k: T,
    limit: T,
) -> Option<T>
where
    for<'x> &'x T: core::ops::Rem<&'x T, Output = T>,
{
    let nn = n.checked_mul(&k)?;
    let sn = sqrt(nn).unwrap();
    let (sq, p) = foward_step::<T, N>(nn, k, limit, sn)?;
    let p0 = ((sn - p) / sq) * sq + p;
    let q1 = backward_step(p0, sq, (nn - p0 * p0) / sq, limit, sn)?;
    let result = q1 / gcd(q1, k.unsigned_shl(1));
    if result > T::one() {
        Some(result)
    } else {
        None
    }
}

/// Shanks's square forms factorization
///
/// This function returns `Some(divisor)` on success.
/// Recommended input is `n <= T::MAX / (3 * 5 * 7 * 11)`.
///
/// reference
/// * [Shanks's square forms factorization](https://en.wikipedia.org/wiki/Shanks%27s_square_forms_factorization)
/// * Jason E. Gower, Samuel S. Wagstaff Jr., Square form factorization, <https://doi.org/10.1090/S0025-5718-07-02010-8>
/// * [素因数分解アルゴリズム(特にSQUFOF)のこと](https://lemniscus.hatenablog.com/entry/20130226/1361874593)
///```
///use squfof::square_form_factorization;
///let n = 991 * 997;
///let f = square_form_factorization(n).unwrap();
///assert!(f == 991 || f == 997);
///```
pub fn square_form_factorization<T: PrimInt + Step>(n: T) -> Option<T>
where
    for<'x> &'x T: core::ops::Rem<&'x T, Output = T>,
{
    let two = T::from(2).unwrap();
    if n < two {
        return None;
    }
    for p in [2, 3, 5, 7, 11] {
        if let Some(p) = T::from(p) {
            if (n % p).is_zero() {
                return Some(p);
            }
        }
    }
    let sn = sqrt(n).unwrap();
    if sn * sn == n {
        return Some(sn);
    }
    let l = two * sqrt(two * sn).unwrap();
    const KS: [i16; 16] = [
        1,
        3,
        5,
        7,
        11,
        3 * 5,
        3 * 7,
        3 * 11,
        5 * 7,
        5 * 11,
        7 * 11,
        3 * 5 * 7,
        3 * 5 * 11,
        3 * 7 * 11,
        5 * 7 * 11,
        3 * 5 * 7 * 11,
    ];
    for k in KS {
        if let Some(k) = T::from(k) {
            let f = square_form_factorization_aux::<T, 64>(n, k, l);
            if f.is_some() {
                return f;
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use crate::*;
    use rayon::prelude::*;
    #[test]
    fn squfof_u32_1() {
        use is_prime_for_primitive_int::IsPrime;
        use rand::prelude::*;
        let mut rng = rand::thread_rng();
        for _ in 0..1_000_000 {
            let mut n: u32 = rng.gen();
            n >>= 11;
            if n < 2 || n.is_prime() {
                continue;
            }
            let f = square_form_factorization(n).unwrap();
            assert!(n % f == 0);
        }
    }
    #[test]
    fn squfof_u32_2() {
        use is_prime_for_primitive_int::IsPrime;
        use rand::prelude::*;
        let mut rng = rand::thread_rng();
        for _ in 0..1_000_000 {
            let n: u32 = rng.gen();
            if n < 2 || n.is_prime() {
                continue;
            }
            if let Some(f) = square_form_factorization(n) {
                assert!(n % f == 0);
            }
        }
    }
    #[test]
    fn squfof_u64_1() {
        use is_prime_for_primitive_int::IsPrime;
        use rand::prelude::*;
        let mut rng = rand::thread_rng();
        for _ in 0..10_000 {
            let mut n: u64 = rng.gen();
            n >>= 11;
            if n < 2 || n.is_prime() {
                continue;
            }
            let f = square_form_factorization(n).unwrap();
            assert!(n % f == 0);
        }
    }
    #[test]
    fn squfof_u64_2() {
        use is_prime_for_primitive_int::IsPrime;
        use rand::prelude::*;
        let mut rng = rand::thread_rng();
        for _ in 0..10_000 {
            let n: u64 = rng.gen();
            if n < 2 || n.is_prime() {
                continue;
            }
            if let Some(f) = square_form_factorization(n) {
                assert!(n % f == 0);
            }
        }
    }
    fn gen_prime(rng: &mut impl rand::Rng) -> u64 {
        use is_prime_for_primitive_int::IsPrime;
        loop {
            let p = rng.gen::<u64>() >> 17;
            if p.is_prime() {
                return p;
            }
        }
    }
    #[test]
    fn squfof_pq() {
        let mut rng = rand::thread_rng();
        let v = (0..100)
            .into_iter()
            .map(|_| (gen_prime(&mut rng), gen_prime(&mut rng)))
            .collect::<Vec<_>>();
        v.into_par_iter().for_each(|(p, q)| {
            dbg!(p, q);
            let n = p as u128 * q as u128;
            dbg!(n);
            let f = square_form_factorization(n).unwrap();
            assert!(f == (p as u128) || f == (q as u128));
        });
    }
}
