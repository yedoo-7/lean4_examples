import Mathlib

/-!
# 一次一密 (One-Time Pad) 的完美保密性 / Perfect secrecy of the one-time pad

This file formalizes Shannon's perfect secrecy of the one-time pad.

The cipher: the key space, message space and ciphertext space are all a finite
group `G`; encryption of a message `m` under a key `k` is `m * k`
(for `G = (Fin n → ZMod 2)` with addition this is the usual bitwise XOR pad).

Perfect secrecy says: when the key is drawn uniformly at random, the
distribution of the ciphertext is the uniform distribution, *whatever* the
message is.  Consequently the ciphertext distributions of any two messages are
identical, so a ciphertext carries no information about the plaintext.
-/

namespace Crypto.OneTimePad

variable {G : Type*} [Fintype G]

/-- Encrypting a fixed message with a uniformly random key produces a uniformly
distributed ciphertext (multiplicative version). -/
theorem map_uniform_mul_left [Group G] (m : G) :
    (PMF.uniformOfFintype G).map (fun k => m * k) = PMF.uniformOfFintype G := by
  ext c
  rw [PMF.map_apply,
    tsum_eq_single (m⁻¹ * c) (by intro b hb; simp only [ite_eq_right_iff]
                                 intro h; exact absurd (by rw [h]; group) hb)]
  simp

/-- Encrypting a fixed message with a uniformly random key produces a uniformly
distributed ciphertext (additive version, e.g. the XOR pad). -/
theorem map_uniform_add_left [AddGroup G] (m : G) :
    (PMF.uniformOfFintype G).map (fun k => m + k) = PMF.uniformOfFintype G := by
  ext c
  rw [PMF.map_apply,
    tsum_eq_single (-m + c) (by intro b hb; simp only [ite_eq_right_iff]
                                intro h; exact absurd (by rw [h]; simp) hb)]
  simp

/-- **Perfect secrecy**: the ciphertext distribution is the same for any two
messages, hence the ciphertext reveals nothing about the message. -/
theorem perfect_secrecy [Group G] (m m' : G) :
    (PMF.uniformOfFintype G).map (fun k => m * k)
      = (PMF.uniformOfFintype G).map (fun k => m' * k) := by
  rw [map_uniform_mul_left, map_uniform_mul_left]

/-- **Perfect secrecy**, additive (XOR) version. -/
theorem perfect_secrecy_add [AddGroup G] (m m' : G) :
    (PMF.uniformOfFintype G).map (fun k => m + k)
      = (PMF.uniformOfFintype G).map (fun k => m' + k) := by
  rw [map_uniform_add_left, map_uniform_add_left]

/-- Whatever the prior distribution `prior` of the plaintext is, the resulting
ciphertext is uniformly distributed; the ciphertext distribution therefore does
not depend on the plaintext distribution at all. -/
theorem ciphertext_dist_eq_uniform [Group G] (prior : PMF G) :
    (prior.bind fun m => (PMF.uniformOfFintype G).map fun k => m * k)
      = PMF.uniformOfFintype G := by
  simp [map_uniform_mul_left]

omit [Fintype G] in
/-- Counting form of perfect secrecy: for every message `m` and ciphertext `c`
there is exactly one key mapping `m` to `c`, so all messages are equally
consistent with a given ciphertext. -/
theorem ncard_keys_eq_one [Group G] (m c : G) :
    {k : G | m * k = c}.ncard = 1 := by
  have : {k : G | m * k = c} = {m⁻¹ * c} := by
    ext k; simp [Set.mem_setOf_eq, eq_inv_mul_iff_mul_eq]
  rw [this, Set.ncard_singleton]

omit [Fintype G] in
/-- Correctness of the one-time pad: decryption undoes encryption. -/
theorem decrypt_encrypt [Group G] (m k : G) : (m * k) * k⁻¹ = m := by
  simp

end Crypto.OneTimePad
