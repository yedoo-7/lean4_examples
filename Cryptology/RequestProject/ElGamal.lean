import RequestProject.OneTimePad

/-!
# Diffie–Hellman、ElGamal 与 Pedersen 承诺 / DH key agreement, ElGamal, Pedersen

Elementary but genuinely machine-checked statements about group-based
cryptographic schemes.
-/

namespace Crypto.ElGamal

variable {G : Type*} [CommGroup G]

/-- **Diffie–Hellman key agreement**: both parties compute the same shared
secret. -/
theorem dh_agree (g : G) (a b : ℕ) : (g ^ a) ^ b = (g ^ b) ^ a := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- ElGamal encryption of `m` under public key `pk = g ^ x` with randomness
`r`. -/
def enc (g : G) (pk : G) (m : G) (r : ℕ) : G × G := (g ^ r, m * pk ^ r)

/-- ElGamal decryption with secret key `x`. -/
def dec (x : ℕ) (c : G × G) : G := c.2 * (c.1 ^ x)⁻¹

/-- **ElGamal correctness**: decryption with the secret key `x` recovers the
message encrypted under the public key `g ^ x`. -/
theorem dec_enc (g : G) (x : ℕ) (m : G) (r : ℕ) : dec x (enc g (g ^ x) m r) = m := by
  simp [enc, dec, ← pow_mul, Nat.mul_comm]

/-- **Pedersen commitment is perfectly hiding**: with a uniformly random
blinding factor the commitment `g ^ m * h` to a message is uniformly
distributed, hence independent of the committed value. -/
theorem pedersen_perfectly_hiding [Fintype G] (c c' : G) :
    (PMF.uniformOfFintype G).map (fun h => c * h)
      = (PMF.uniformOfFintype G).map (fun h => c' * h) :=
  Crypto.OneTimePad.perfect_secrecy c c'

end Crypto.ElGamal
