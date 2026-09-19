import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000

/-!
# 形式化内核：基于数据-地理位置联合驱动的 5G 微基站最优分配策略（张朝辉、李靖、韩璐珩，2022）

该论文的算法主体是启发式贪婪算法，整体优化模型 (13)–(19) 是 NP 难整数非线性规划。
其可严格形式化、并给出闭式最优解的**数学内核**是"最优蜂窝单元数量"的推导
（式 (9)–(11)）：每轮总能耗可写成

  `E(k) = A·k + B/k + C`,  （`A,B>0` 为与网络规模、能耗系数有关的常数）

对蜂窝单元数 `k` 求最小值。由均值不等式 (AM–GM)，最优值在 `k* = √(B/A)` 取得，
最小能耗为 `2√(AB) + C`。这正是论文式 (10)、(11) 给出最优蜂窝单元数量公式的根据。
-/

namespace FiveGAllocation

/-
能耗下界（AM–GM）：对 `A,B>0` 及任意 `k>0`，有 `A·k + B/k ≥ 2√(AB)`。
-/
theorem energy_lower_bound (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∀ k : ℝ, 0 < k → 2 * Real.sqrt (A * B) ≤ A * k + B / k := by
  intros k hk;
  rw [ add_div', le_div_iff₀ ] <;> nlinarith [ sq_nonneg ( k * A - Real.sqrt ( A * B ) ), Real.mul_self_sqrt ( mul_nonneg hA.le hB.le ) ]

/-
在 `k* = √(B/A)` 处下界被取到：`A·k* + B/k* = 2√(AB)`。
故 `k* = √(B/A)` 是 `E(k)=A·k+B/k`（式 (9) 的核心部分）的最小值点，
对应论文式 (10)、(11) 的最优蜂窝单元数量。
-/
theorem energy_min_value (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    A * Real.sqrt (B / A) + B / Real.sqrt (B / A) = 2 * Real.sqrt (A * B) := by
  norm_num [ mul_div_cancel₀, hA.le, hB.le, hA.ne', hB.ne' ] ; ring_nf;
  grind +ring

/-
综合：`k* = √(B/A)` 是能耗 `E(k)=A·k+B/k`（`k>0`）的全局最小值点。
-/
theorem energy_argmin (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∀ k : ℝ, 0 < k →
      A * Real.sqrt (B / A) + B / Real.sqrt (B / A) ≤ A * k + B / k := by
  exact fun k hk => by rw [ energy_min_value A B hA hB ] ; exact energy_lower_bound A B hA hB k hk;

end FiveGAllocation