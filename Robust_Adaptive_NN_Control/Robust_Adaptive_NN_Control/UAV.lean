import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

/-!
# 形式化内核：面向未知拒止环境的分布式自适应多无人机协同航迹规划（徐奇琛、张朝辉、李靖，2026）

该论文是一篇工程/启发式算法论文（麻雀搜索算法 + 适应度函数 + UAV 视线避障），
不含传统意义上的"定理 + 证明"。其可被严格形式化的**数学内核**主要是几条
关于评分/归一化函数有界性与运动学约束的命题。本文件形式化其中三条：

1. `desired_velocity_norm_le`：期望速度限幅式 (2)
   `v_d = (v/‖v‖)·min(v_max, ‖v‖)` 的范数恰为 `min(v_max,‖v‖) ≤ v_max`，
   即输出确实满足物理速度上限约束。
2. `Fdire_score_mem`：方向一致性评分式 (10) `F_dire = exp(Φ/2 − 1)`，
   其中 `Φ = cos(·) ∈ [−1,1]`，故 `F_dire ∈ (0,1)`，落在论文声称的 `[0,1]` 内。
3. `theta_mem`：式 (13) 给出的 heaviside 连续近似
   `Θ(x) = 1/2 + 16x / (2 ln(e^{−16x}+e^{16x}))` 的值域为 `(0,1)`，
   即它确实是一个取值在 `(0,1)` 的光滑阶跃近似。
-/

namespace UAVPathPlanning

/-
式 (2)：限幅后的期望速度 `v_d = (v/‖v‖)·min(v_max,‖v‖)`（当 `v ≠ 0`）的范数
等于 `min(v_max,‖v‖)`，从而不超过物理上限 `v_max`。
-/
theorem desired_velocity_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : V) (vmax : ℝ) (hv : v ≠ 0) (hvmax : 0 ≤ vmax) :
    ‖(min vmax ‖v‖ / ‖v‖) • v‖ = min vmax ‖v‖ ∧ ‖(min vmax ‖v‖ / ‖v‖) • v‖ ≤ vmax := by
  simp +decide [ norm_smul, hv, hvmax ];
  rw [ abs_of_nonneg ( by positivity ) ] ; exact min_le_left _ _

/-
式 (10)：方向一致性评分 `F_dire = exp(Φ/2 − 1)`，其中 `Φ` 为夹角余弦 `∈ [−1,1]`。
则 `F_dire ∈ (0,1)`，因此落在论文声称的 `[0,1]` 内。
（事实上只需 `Φ ≤ 1`，下界 `−1 ≤ Φ` 对结论不必要，故不作为假设列出。）
-/
theorem Fdire_score_mem (c : ℝ) (h2 : c ≤ 1) :
    Real.exp (c / 2 - 1) ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨ Real.exp_pos _, Real.exp_lt_one_iff.mpr <| by linarith ⟩

/-- 式 (13) 中的 heaviside 连续近似函数 `Θ`。 -/
noncomputable def theta (x : ℝ) : ℝ :=
  1 / 2 + (16 * x) / (2 * Real.log (Real.exp (-16 * x) + Real.exp (16 * x)))

/-
关键不等式：对任意实数 `a`，有 `|a| < log (e^{−a} + e^{a})`。
（因为 `e^{−a}+e^{a} > e^{|a|}`，对其取对数即得。）
-/
theorem abs_lt_log_exp_add_exp (a : ℝ) :
    |a| < Real.log (Real.exp (-a) + Real.exp a) := by
  cases abs_cases a <;> simp +decide [ * ]; all_goals rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.exp_pos ( -a ), Real.exp_pos a ]

/-
式 (13)：归一化函数 `Θ(x)` 的值域为开区间 `(0,1)`，
确实是取值于 `(0,1)` 的光滑阶跃（heaviside）近似。
-/
theorem theta_mem (x : ℝ) : theta x ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold theta;
  have := abs_lt_log_exp_add_exp ( 16 * x ) ; norm_num at * ; constructor <;> ring_nf at *;
  · cases abs_cases x <;> nlinarith [ inv_pos.mpr ( show 0 < Real.log ( Real.exp ( - ( x * 16 ) ) + Real.exp ( x * 16 ) ) from lt_of_le_of_lt ( by positivity ) this ), mul_inv_cancel₀ ( ne_of_gt ( show 0 < Real.log ( Real.exp ( - ( x * 16 ) ) + Real.exp ( x * 16 ) ) from lt_of_le_of_lt ( by positivity ) this ) ) ];
  · cases abs_cases x <;> nlinarith [ inv_mul_cancel₀ ( by linarith : Real.log ( Real.exp ( - ( x * 16 ) ) + Real.exp ( x * 16 ) ) ≠ 0 ) ]

end UAVPathPlanning