import Mathlib

open scoped RealInnerProductSpace

set_option maxHeartbeats 4000000

/-!
# 形式化内核：基于无线通信基站的室内三维定位问题（张朝辉等，2017）

该论文是一篇（华为杯）数学建模竞赛论文，核心方法是 TOA 三边/多边测量定位：
把若干"球面方程" `‖p − q_i‖² = d_i²` 两两相减线性化为超定线性方程组 `A x ≈ B`，
再用**最小二乘法**求解（式 (8)、(13)）：`x* = (AᵀA)⁻¹ AᵀB`。

其可严格形式化的**数学内核**是最小二乘解的最优性：
满足**正规方程** `Aᵀ(A x* − b) = 0` 的点 `x*` 使残差 `‖A x − b‖` 取得最小值。
这正是式 (8)、(13) 中闭式解 `(AᵀA)⁻¹Aᵀb` 之所以为最优估计的根本原因。

证明用勾股分解：
`‖A x − b‖² = ‖A(x − x*)‖² + ‖A x* − b‖² ≥ ‖A x* − b‖²`。
-/

namespace IndoorPositioning

/-
最小二乘正规方程解的最优性（式 (8)、(13) 的数学内核）。
若 `x₀` 满足正规方程 `∀ v, ⟪A v, A x₀ − b⟫ = 0`，
则 `x₀` 在所有 `x` 中使残差范数 `‖A x − b‖` 取最小值。
-/
theorem least_squares_normal_eq_minimizer
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →ₗ[ℝ] F) (b : F) (x₀ : E)
    (hortho : ∀ v : E, ⟪A v, A x₀ - b⟫ = (0 : ℝ)) :
    ∀ x : E, ‖A x₀ - b‖ ≤ ‖A x - b‖ := by
  intro x
  have h_norm : ‖A x - b‖^2 = ‖A (x - x₀)‖^2 + ‖A x₀ - b‖^2 := by
    simp +decide [ *, norm_sub_sq_real ];
    have := hortho x; have := hortho x₀; simp_all +decide [ inner_sub_right ] ;
    linarith [ hortho x ];
  nlinarith [ norm_nonneg ( A x - b ), norm_nonneg ( A ( x - x₀ ) ) ]

/-
勾股分解（上一定理的核心步骤，单独陈述以备复用）：
在正规方程成立时，`‖A x − b‖² = ‖A (x − x₀)‖² + ‖A x₀ − b‖²`。
-/
theorem residual_pythagoras
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →ₗ[ℝ] F) (b : F) (x₀ : E)
    (hortho : ∀ v : E, ⟪A v, A x₀ - b⟫ = (0 : ℝ)) :
    ∀ x : E, ‖A x - b‖ ^ 2 = ‖A (x - x₀)‖ ^ 2 + ‖A x₀ - b‖ ^ 2 := by
  intro x
  have h_decomp : A x - b = A (x - x₀) + (A x₀ - b) := by
    simp +decide [ sub_eq_add_neg, add_assoc ];
  rw [ h_decomp, @norm_add_sq ℝ ];
  grind +qlia

end IndoorPositioning