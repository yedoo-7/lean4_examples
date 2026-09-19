import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# 二分法（Bisection method）的形式化

对连续函数 `f`，若 `f a ≤ 0 ≤ f b`，二分法给出一列区间 `[aₙ, bₙ]`，
其长度按 `2⁻ⁿ` 收缩，且每个区间内都含有 `f` 的一个零点。
证明：

* `Bisection.width_iter`：`bₙ - aₙ = (b - a) / 2 ^ n`；
* `Bisection.exists_root_iter`：每个区间 `[aₙ, bₙ]` 内都有零点；
* `Bisection.midpoint_error_le`：第 `n` 步的中点与某个真实零点的距离 `≤ (b - a) / 2 ^ (n+1)`；
* `Bisection.tendsto_error`：误差界收敛到 `0`（即算法收敛）。
-/

namespace Numerics.Bisection

open Set Filter Topology

variable (f : ℝ → ℝ)

/-- 二分法的一步：取中点 `m`，根据 `f m` 的符号保留含零点的半区间。 -/
noncomputable def step (p : ℝ × ℝ) : ℝ × ℝ :=
  if f ((p.1 + p.2) / 2) ≤ 0 then (((p.1 + p.2) / 2), p.2) else (p.1, ((p.1 + p.2) / 2))

/-- 迭代 `n` 步之后的区间。 -/
noncomputable def iter (p : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => p
  | n + 1 => step f (iter p n)

/-- 第 `n` 步区间的中点，即算法给出的第 `n` 个近似根。 -/
noncomputable def approx (p : ℝ × ℝ) (n : ℕ) : ℝ :=
  ((iter f p n).1 + (iter f p n).2) / 2

@[simp] lemma iter_zero (p : ℝ × ℝ) : iter f p 0 = p := rfl

@[simp] lemma iter_succ (p : ℝ × ℝ) (n : ℕ) : iter f p (n + 1) = step f (iter f p n) := rfl

lemma width_step (p : ℝ × ℝ) : (step f p).2 - (step f p).1 = (p.2 - p.1) / 2 := by
  unfold step; split_ifs <;> simp <;> ring

/-- 区间长度每步减半。 -/
lemma width_iter (p : ℝ × ℝ) (n : ℕ) :
    (iter f p n).2 - (iter f p n).1 = (p.2 - p.1) / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [iter_succ, width_step, ih]; ring

/-- 每一步得到的区间包含于上一步的区间。 -/
lemma step_subset {p : ℝ × ℝ} (h : p.1 ≤ p.2) :
    p.1 ≤ (step f p).1 ∧ (step f p).1 ≤ (step f p).2 ∧ (step f p).2 ≤ p.2 := by
  unfold step; split_ifs <;> simp <;> constructor <;> linarith

lemma le_iter (p : ℝ × ℝ) (h : p.1 ≤ p.2) (n : ℕ) : (iter f p n).1 ≤ (iter f p n).2 := by
  induction n with
  | zero => simpa using h
  | succ n ih => exact (step_subset f ih).2.1

/-- 迭代区间始终包含在初始区间内。 -/
lemma iter_subset (p : ℝ × ℝ) (h : p.1 ≤ p.2) (n : ℕ) :
    Icc (iter f p n).1 (iter f p n).2 ⊆ Icc p.1 p.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      refine subset_trans ?_ ih
      have h1 := step_subset f (le_iter f p h n)
      exact Icc_subset_Icc h1.1 h1.2.2

/-- 变号条件 `f a ≤ 0 ≤ f b` 在迭代中保持。 -/
lemma sign_iter (p : ℝ × ℝ) (h1 : f p.1 ≤ 0) (h2 : 0 ≤ f p.2) (n : ℕ) :
    f (iter f p n).1 ≤ 0 ∧ 0 ≤ f (iter f p n).2 := by
  induction n with
  | zero => exact ⟨h1, h2⟩
  | succ n ih =>
      rw [iter_succ]
      unfold step
      split_ifs with hm
      · exact ⟨hm, ih.2⟩
      · exact ⟨ih.1, le_of_lt (not_le.1 hm)⟩

/-- **每个迭代区间内都存在真实零点。** -/
theorem exists_root_iter (p : ℝ × ℝ) (h : p.1 ≤ p.2)
    (hc : ContinuousOn f (Icc p.1 p.2)) (h1 : f p.1 ≤ 0) (h2 : 0 ≤ f p.2) (n : ℕ) :
    ∃ r ∈ Icc (iter f p n).1 (iter f p n).2, f r = 0 := by
  have hsub := iter_subset f p h n
  have hle := le_iter f p h n
  have hsign := sign_iter f p h1 h2 n
  have hc' : ContinuousOn f (Icc (iter f p n).1 (iter f p n).2) := hc.mono hsub
  have : (0 : ℝ) ∈ f '' Icc (iter f p n).1 (iter f p n).2 :=
    intermediate_value_Icc hle hc' ⟨hsign.1, hsign.2⟩
  obtain ⟨r, hr, hfr⟩ := this
  exact ⟨r, hr, hfr⟩

/-- **误差估计**：第 `n` 步的中点与某个真实零点的距离不超过 `(b - a) / 2 ^ (n+1)`。 -/
theorem midpoint_error_le (p : ℝ × ℝ) (h : p.1 ≤ p.2)
    (hc : ContinuousOn f (Icc p.1 p.2)) (h1 : f p.1 ≤ 0) (h2 : 0 ≤ f p.2) (n : ℕ) :
    ∃ r, f r = 0 ∧ r ∈ Icc p.1 p.2 ∧ |approx f p n - r| ≤ (p.2 - p.1) / 2 ^ (n + 1) := by
  obtain ⟨r, hr, hfr⟩ := exists_root_iter f p h hc h1 h2 n
  refine ⟨r, hfr, iter_subset f p h n hr, ?_⟩
  have hw := width_iter f p n
  have h1' := hr.1
  have h2' := hr.2
  rw [abs_le]
  unfold approx
  constructor
  · have : (p.2 - p.1) / 2 ^ (n + 1) = ((iter f p n).2 - (iter f p n).1) / 2 := by
      rw [hw]; ring
    rw [this]; linarith
  · have : (p.2 - p.1) / 2 ^ (n + 1) = ((iter f p n).2 - (iter f p n).1) / 2 := by
      rw [hw]; ring
    rw [this]; linarith

/-- 误差界随迭代次数趋于零：二分法收敛。 -/
theorem tendsto_error (p : ℝ × ℝ) :
    Tendsto (fun n : ℕ => (p.2 - p.1) / 2 ^ (n + 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (p.2 - p.1) * ((1 / 2 : ℝ) ^ (n + 1))) atTop (𝓝 ((p.2 - p.1) * 0)) := by
    refine Filter.Tendsto.const_mul _ ?_
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num))
    exact this.comp (Filter.tendsto_add_atTop_nat 1)
  simpa [div_eq_mul_inv, one_div, inv_pow, mul_comm] using h

/-- 对任意精度 `ε > 0`，存在迭代步数使近似根的误差小于 `ε`。 -/
theorem exists_iterate_error_lt (p : ℝ × ℝ) (h : p.1 ≤ p.2)
    (hc : ContinuousOn f (Icc p.1 p.2)) (h1 : f p.1 ≤ 0) (h2 : 0 ≤ f p.2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∃ r, f r = 0 ∧ |approx f p n - r| < ε := by
  obtain ⟨n, hn⟩ := ((tendsto_error p).eventually (eventually_lt_nhds hε)).exists
  obtain ⟨r, hfr, _, hle⟩ := midpoint_error_le f p h hc h1 h2 n
  exact ⟨n, r, hfr, lt_of_le_of_lt hle hn⟩

end Numerics.Bisection
