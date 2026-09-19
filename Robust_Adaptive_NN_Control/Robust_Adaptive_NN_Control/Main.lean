import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# 形式化内核：未知离散非线性系统鲁棒自适应 NN 控制（李靖、李俊民，2003）

本文件形式化该论文稳定性证明（定理 1）的**数学内核**。

论文的 backstepping 设计最终把闭环误差系统写成一个线性时变递推（式(18)）：

  `z(t+1) = A z(t) + b·y_d(t+n) + Σ(t+1) + e(t+1)`,

其中 `A` 是严格稳定多项式 `F(q⁻¹)` 的 companion（友）矩阵，因此是 Schur 稳定的；
而 `b·y_d + Σ + e` 是一个有界的"扰动/不确定性"项，其幅度与建模误差 `μ`、
神经网络权值变化率等不确定性成比例。

定理 1 的两条结论：
  (i) 闭环状态 `z(t)` **全局有界**；
  (ii) 跟踪误差落入一个**大小与不确定性幅度成比例**的紧集中。

这两条本质上都是下面这个离散 ISS（输入到状态稳定）型估计的推论：
对压缩线性系统 `z(t+1) = A z(t) + w(t)`（`‖A‖ ≤ ρ < 1`、`‖w(t)‖ ≤ M`），有

  `‖z(t)‖ ≤ ρ^t ‖z(0)‖ + M/(1-ρ)`,

从而状态一致有界，且渐近界 `M/(1-ρ)` 与扰动幅度 `M` 成正比（`M→0` 时趋于 0）。

下面把这一内核完整形式化并证明。
-/

namespace RobustAdaptiveNN

/-
**核心标量递推界**。
若非负序列满足 `a(t+1) ≤ ρ·a(t) + M`（`0 ≤ ρ < 1`，`M ≥ 0`），
则 `a(t) ≤ ρ^t·a(0) + M/(1-ρ)`。这是离散 ISS 估计的纯实数核心。
-/
lemma recurrence_bound (a : ℕ → ℝ) (ρ M : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 ≤ M)
    (hrec : ∀ t, a (t + 1) ≤ ρ * a t + M) :
    ∀ t, a t ≤ ρ ^ t * a 0 + M / (1 - ρ) := by
  intro t;
  induction' t with t ih <;> norm_num [ pow_succ' ] at *;
  · exact div_nonneg hM ( sub_nonneg.2 hρ1.le );
  · nlinarith [ hrec t, show ρ ^ t ≥ 0 by positivity, show M / ( 1 - ρ ) ≥ 0 by exact div_nonneg hM ( by linarith ), mul_div_cancel₀ M ( by linarith : ( 1 - ρ ) ≠ 0 ) ]

/-
**一致（全局）有界**：在 `a 0 ≥ 0` 时，`a(t) ≤ a(0) + M/(1-ρ)` 对所有 `t` 成立。
-/
lemma recurrence_uniform_bound (a : ℕ → ℝ) (ρ M : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 ≤ M) (ha0 : 0 ≤ a 0)
    (hrec : ∀ t, a (t + 1) ≤ ρ * a t + M) :
    ∀ t, a t ≤ a 0 + M / (1 - ρ) := by
  intro t;
  induction' t with t ih;
  · exact le_add_of_nonneg_right ( div_nonneg hM ( sub_nonneg.2 hρ1.le ) );
  · nlinarith [ hrec t, mul_div_cancel₀ M ( by linarith : ( 1 - ρ ) ≠ 0 ) ]

/-
**赋范空间中的压缩线性系统的 ISS 估计**。
对闭环 `z(t+1) = A(z t) + w t`，若算子范数 `‖A‖ ≤ ρ < 1` 且扰动 `‖w t‖ ≤ M`，
则 `‖z t‖ ≤ ρ^t·‖z 0‖ + M/(1-ρ)`。
-/
lemma linear_system_iss
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (z w : ℕ → E) (ρ M : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 ≤ M)
    (hA : ‖A‖ ≤ ρ)
    (hrec : ∀ t, z (t + 1) = A (z t) + w t)
    (hw : ∀ t, ‖w t‖ ≤ M) :
    ∀ t, ‖z t‖ ≤ ρ ^ t * ‖z 0‖ + M / (1 - ρ) := by
  convert recurrence_bound _ _ _ _ _ _ _;
  · exact hρ0;
  · exact hρ1;
  · exact hM;
  · exact fun t => by rw [ hrec ] ; exact le_trans ( norm_add_le _ _ ) ( add_le_add ( le_trans ( ContinuousLinearMap.le_opNorm _ _ ) ( mul_le_mul_of_nonneg_right hA ( norm_nonneg _ ) ) ) ( hw _ ) ) ;

/-
**定理 1(i) 的内核：闭环状态全局有界**。
存在常数 `B`（可取 `‖z 0‖ + M/(1-ρ)`）使得 `‖z t‖ ≤ B` 对所有 `t` 成立。
-/
theorem closed_loop_globally_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (z w : ℕ → E) (ρ M : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 ≤ M)
    (hA : ‖A‖ ≤ ρ)
    (hrec : ∀ t, z (t + 1) = A (z t) + w t)
    (hw : ∀ t, ‖w t‖ ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, ‖z t‖ ≤ B := by
  refine' ⟨ ρ ^ 0 * ‖z 0‖ + M / ( 1 - ρ ), _, fun t => _ ⟩;
  · exact add_nonneg ( mul_nonneg ( pow_nonneg hρ0 _ ) ( norm_nonneg _ ) ) ( div_nonneg hM ( sub_nonneg.2 hρ1.le ) );
  · have := linear_system_iss A z w ρ M hρ0 hρ1 hM hA hrec hw t;
    exact this.trans ( add_le_add ( mul_le_mul_of_nonneg_right ( pow_le_one₀ hρ0 hρ1.le ) ( norm_nonneg _ ) ) le_rfl )

/-
**定理 1(ii) 的内核：跟踪误差落入与不确定性幅度成比例的紧集**。
渐近上界为 `M/(1-ρ)`：对任意 `ε > 0`，存在时刻 `T`，使得 `t ≥ T` 后
`‖z t‖ ≤ M/(1-ρ) + ε`。该界与不确定性幅度 `M` 成正比，`M = 0` 时收敛到 `0`。
-/
theorem tracking_error_proportional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (z w : ℕ → E) (ρ M : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 ≤ M)
    (hA : ‖A‖ ≤ ρ)
    (hrec : ∀ t, z (t + 1) = A (z t) + w t)
    (hw : ∀ t, ‖w t‖ ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ t ≥ T, ‖z t‖ ≤ M / (1 - ρ) + ε := by
  -- From Linear System ISS, we have that ‖z t‖ ≤ ρ^t * ‖z 0‖ + M / (1 - ρ).
  have h_bound : ∀ t, ‖z t‖ ≤ ρ ^ t * ‖z 0‖ + M / (1 - ρ) := by
    exact fun t => linear_system_iss A z w ρ M hρ0 hρ1 hM hA hrec hw t;
  -- Given ε > 0, we want to find T such that for t ≥ T, ρ^t * ‖z 0‖ ≤ ε.
  intro ε hεpos
  have h_eventually : ∃ T, ∀ t ≥ T, ρ ^ t * ‖z 0‖ ≤ ε := by
    simpa using ( summable_geometric_of_lt_one hρ0 hρ1 ) |> fun h => h.mul_right _ |> fun h => h.tendsto_atTop_zero.eventually ( ge_mem_nhds hεpos );
  exact ⟨ h_eventually.choose, fun t ht => by linarith [ h_bound t, h_eventually.choose_spec t ht ] ⟩

end RobustAdaptiveNN