import Mathlib

/-!
# Shamir 门限秘密共享 (2-out-of-n) / Shamir secret sharing, threshold 2

Over a finite field `F` the dealer picks a uniformly random `r` and hands the
share `a + r * x` to the participant with (nonzero, pairwise distinct)
evaluation point `x`, where `a` is the secret.

* `reconstruct` : any *two* shares determine the secret;
* `share_dist_eq_uniform` / `single_share_perfect_privacy` : a *single* share is
  uniformly distributed and hence carries no information about the secret.
-/

namespace Crypto.Shamir

variable {F : Type*} [Field F]

/-- **Reconstruction**: two shares of the linear polynomial `a + r * X`, taken
at distinct points `x1 ≠ x2`, determine the secret `a`. -/
theorem reconstruct (a r x1 x2 : F) (h : x1 ≠ x2) :
    ((a + r * x1) * x2 - (a + r * x2) * x1) / (x2 - x1) = a := by
  have hne : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp
  ring

/-- A single share of the secret `a` at a nonzero evaluation point `x`, computed
with uniformly random `r`, is uniformly distributed. -/
theorem share_dist_eq_uniform [Fintype F] (a x : F) (hx : x ≠ 0) :
    (PMF.uniformOfFintype F).map (fun r => a + r * x) = PMF.uniformOfFintype F := by
  ext c
  rw [PMF.map_apply,
    tsum_eq_single ((c - a) / x) (by
      intro b hb; simp only [ite_eq_right_iff]
      intro h; exact absurd (by field_simp; rw [h]; ring) hb),
    if_pos (by field_simp; ring)]
  simp

/-- **Perfect privacy of one share**: the distribution of a single share is the
same for any two secrets, so one share reveals nothing about the secret. -/
theorem single_share_perfect_privacy [Fintype F] (a a' x : F) (hx : x ≠ 0) :
    (PMF.uniformOfFintype F).map (fun r => a + r * x)
      = (PMF.uniformOfFintype F).map (fun r => a' + r * x) := by
  rw [share_dist_eq_uniform a x hx, share_dist_eq_uniform a' x hx]

end Crypto.Shamir
