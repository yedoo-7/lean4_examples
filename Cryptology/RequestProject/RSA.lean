import Mathlib

/-!
# RSA 的正确性 / Correctness of RSA

Let `p ≠ q` be primes, `n = p * q`, and let the public/private exponents `e, d`
satisfy `e * d = 1 + k * lcm (p-1) (q-1)` (the Carmichael-function form of the
RSA key equation).  Then decryption undoes encryption for *every* message in
`ZMod n`, including those not coprime to `n`.
-/

namespace Crypto.RSA

/-- If `(p-1) ∣ t` then `m ^ (1 + t) = m` in `ZMod p`, for every `m`
(including `m = 0`).  This is Fermat's little theorem in the form used by RSA. -/
theorem pow_succ_eq_self_of_prime {p : ℕ} (hp : p.Prime) {t : ℕ} (ht : (p - 1) ∣ t)
    (m : ZMod p) : m ^ (1 + t) = m := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, rfl⟩ := ht
  rcases eq_or_ne m 0 with rfl | hm
  · rw [zero_pow (by omega)]
  · rw [pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one hm, one_pow, mul_one]

/-- **RSA correctness**: with `n = p * q` for distinct primes `p, q` and
`e * d = 1 + k * lcm (p-1) (q-1)`, we have `(m ^ e) ^ d = m` for all
`m : ZMod (p * q)`. -/
theorem rsa_correct {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {e d k : ℕ} (hed : e * d = 1 + k * Nat.lcm (p - 1) (q - 1))
    (m : ZMod (p * q)) : (m ^ e) ^ d = m := by
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  rw [← pow_mul, hed]
  let f := ZMod.chineseRemainder hco
  apply f.injective
  rw [map_pow]
  have h1 : (f m).1 ^ (1 + k * Nat.lcm (p - 1) (q - 1)) = (f m).1 :=
    pow_succ_eq_self_of_prime hp (Dvd.dvd.mul_left (Nat.dvd_lcm_left _ _) k) _
  have h2 : (f m).2 ^ (1 + k * Nat.lcm (p - 1) (q - 1)) = (f m).2 :=
    pow_succ_eq_self_of_prime hq (Dvd.dvd.mul_left (Nat.dvd_lcm_right _ _) k) _
  exact Prod.ext (by simpa using h1) (by simpa using h2)

/-- A concrete sanity check: with `p = 11`, `q = 13`, `e = 7`, `d = 103`
(`7 * 103 = 1 + 12 * lcm 10 12`), RSA decryption recovers the message. -/
example (m : ZMod 143) : (m ^ 7) ^ 103 = m :=
  rsa_correct (p := 11) (q := 13) (by norm_num) (by norm_num) (by norm_num)
    (e := 7) (d := 103) (k := 12) (by norm_num) m

end Crypto.RSA
