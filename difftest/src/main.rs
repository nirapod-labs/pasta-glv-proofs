//! Differential test: pasta_curves' `wnaf_digits`, copied verbatim (src/glv.rs at e3c0f0246f,
//! lines 392-419; CI compares the bytes), run on a fixed input list. The copied code is
//! Copyright The Electric Coin Company and the pasta_curves contributors, MIT OR Apache-2.0.
//!
//! `glv-difftest inputs` prints the inputs, one per line. `glv-difftest run FILE` prints, for
//! each input `a` of FILE and each `negate` in {0, 1}, the line `a negate panic` if the call
//! panics, or `a negate n d0 d1 …` with the returned `(digits, n)`, the digits up to the last
//! nonzero one (all later digits are zero, so nothing is lost).

use std::io::{BufRead, BufReader, Write};

// BEGIN VERBATIM src/glv.rs 392-419
/// Upper bound on the number of width-4 wNAF digits of a decomposition half:
/// an n-bit magnitude yields at most n + 1 digits, and [`decompose`] bounds
/// the halves below `2^127`.
const MAX_WNAF_DIGITS: usize = 128;

/// Width-4 wNAF digits of a u128 magnitude, lowest position first, with the
/// half's overall sign folded into the digits when `negate` is set.
fn wnaf_digits(a: u128, negate: bool) -> ([i8; MAX_WNAF_DIGITS], usize) {
    debug_assert!(a >> 127 == 0, "magnitude must be at most 127 bits");
    let mut digits = [0i8; MAX_WNAF_DIGITS];
    let mut n = 0;
    let mut k = a;
    while k != 0 {
        if k & 1 == 1 {
            let low = (k & 0xF) as i8;
            let d = if low >= 8 { low - 16 } else { low };
            digits[n] = if negate { -d } else { d };
            if d >= 0 {
                k -= d as u128;
            } else {
                k += (-d) as u128;
            }
        }
        n += 1;
        k >>= 1;
    }
    (digits, n)
}
// END VERBATIM

/// The least magnitude whose wNAF needs a 129th digit.
const S: u128 = 0x88888888888888888888888888888889;

/// SplitMix64, a fixed-seed generator, so the input list is the same on every run.
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

/// Every magnitude below 2^16, the neighbours of every power of two, every repeated-nibble
/// pattern, the small cases of the 0x88...89 pattern, the neighbourhoods of 2^127, of S and of
/// u128::MAX, then 10,000 random magnitudes of uniformly random bit length (0 to 128 bits).
/// Repeats are dropped.
fn inputs() -> Vec<u128> {
    let mut v: Vec<u128> = Vec::new();
    for a in 0..(1u128 << 16) {
        v.push(a);
    }
    for k in 1..128u32 {
        let p = 1u128 << k;
        v.extend([p - 1, p, p + 1]);
    }
    for nibble in 1..16u128 {
        let mut a = 0u128;
        for _ in 0..32 {
            a = (a << 4) | nibble;
            v.push(a);
        }
    }
    for a in [0x88u128, 0x89, 0x888, 0x889, 0x8888, 0x8889] {
        v.push(a);
    }
    for center in [1u128 << 127, S] {
        for a in center - 64..=center + 64 {
            v.push(a);
        }
    }
    for a in u128::MAX - 64..=u128::MAX {
        v.push(a);
    }
    let mut state = 0x5eed_9174_0003_u64;
    for _ in 0..10_000 {
        let bits = (splitmix64(&mut state) % 129) as u32;
        let raw = (u128::from(splitmix64(&mut state)) << 64) | u128::from(splitmix64(&mut state));
        v.push(if bits == 0 { 0 } else { raw >> (128 - bits) });
    }
    let mut seen = std::collections::HashSet::new();
    v.retain(|a| seen.insert(*a));
    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("inputs") => {
            let out = std::io::stdout();
            let mut out = out.lock();
            for a in inputs() {
                writeln!(out, "{a}").unwrap();
            }
        }
        Some("run") => {
            std::panic::set_hook(Box::new(|_| {}));
            let file = std::fs::File::open(&args[2]).expect("input file");
            let out = std::io::stdout();
            let mut out = out.lock();
            for line in BufReader::new(file).lines() {
                let a: u128 = line.unwrap().trim().parse().expect("a u128");
                for negate in [false, true] {
                    match std::panic::catch_unwind(|| wnaf_digits(a, negate)) {
                        Ok((digits, n)) => {
                            write!(out, "{a} {} {n}", u8::from(negate)).unwrap();
                            let m = digits.iter().rposition(|&d| d != 0).map_or(0, |i| i + 1);
                            for d in &digits[..m] {
                                write!(out, " {d}").unwrap();
                            }
                            writeln!(out).unwrap();
                        }
                        Err(_) => writeln!(out, "{a} {} panic", u8::from(negate)).unwrap(),
                    }
                }
            }
        }
        _ => {
            eprintln!("usage: glv-difftest inputs | glv-difftest run FILE");
            std::process::exit(2);
        }
    }
}
