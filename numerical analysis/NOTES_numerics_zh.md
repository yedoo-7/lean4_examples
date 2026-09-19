# 数值分析可以形式化证明吗？

**可以。** 而且数值分析在很多方面比密码学更"适合"形式化：它的核心命题几乎都是关于实数的
**不等式与误差估计**（收敛性、稳定性、截断误差、舍入误差），这类命题恰好是证明助手擅长处理的对象。

数值分析的形式化大致可以分成三层：

1. **算法的数学性质**：收敛性、误差界、稳定性、可解性判据。
   这一层是纯数学命题，可以在 Lean/Coq/Isabelle 中**无条件地完整证明**。
2. **浮点/舍入误差分析**：在标准舍入模型（`|fl(t) - t| ≤ u |t|`）下的前向/后向误差界。
   同样可以严格证明；更进一步还可以直接对 IEEE-754 浮点语义建模（如 Flocq、Gappa 之类的工作）。
3. **具体实现的验证**：把机器代码/C 代码与规范联系起来，证明实现真的满足上述误差界。
   这一层需要程序验证工具链，工作量最大，但同样是可做的。

本项目在 Lean 4 + Mathlib 中给出了第 1、2 层的**机器验证**示例：全部编译通过，无 `sorry`，
只依赖标准公理 `propext` / `Classical.choice` / `Quot.sound`。

---

## 本项目中已证明的结果

### `RequestProject/Numerics/Bisection.lean` —— 二分法（求根）
* `width_iter`：区间长度精确按 `2⁻ⁿ` 收缩，`bₙ - aₙ = (b - a) / 2ⁿ`。
* `exists_root_iter`：每个迭代区间内都确实存在 `f` 的零点（用介值定理，并证明变号条件在迭代中保持）。
* `midpoint_error_le`：第 `n` 步的中点与某个**真实零点**的距离 `≤ (b - a) / 2ⁿ⁺¹`。
* `tendsto_error`、`exists_iterate_error_lt`：误差界趋于零，任给精度都能在有限步内达到。

### `RequestProject/Numerics/FixedPoint.lean` —— 不动点迭代与 Newton 开平方
* `FixedPoint.exists_unique_fixedPoint`：压缩映射在完备空间上不动点存在且唯一（Banach）。
* `FixedPoint.dist_iterate_le`：`|xₙ - x*| ≤ Kⁿ |x₀ - x*|`（线性收敛）。
* `FixedPoint.apriori_bound`、`FixedPoint.tendsto_iterate`：先验误差估计与迭代收敛性。
* 巴比伦（Newton）开平方 `xₙ₊₁ = (xₙ + a/xₙ)/2`：
  * `Babylonian.step_sub_sqrt_eq`：误差恒等式 `g(x) - √a = (x - √a)² / (2x)`；
  * `Babylonian.quadratic_convergence`：`eₙ₊₁ ≤ eₙ² / (2√a)`，即**二次收敛**；
  * `Babylonian.error_le_geom`、`Babylonian.tendsto_sqrt`：误差至少每步减半，迭代收敛到 `√a`；
  * `Babylonian.sqrt_two_approx`：具体实例，从 `x₀ = 1` 迭代 3 步得到 `577/408`，
    与 `√2` 的误差 `≤ 2.5 × 10⁻⁶`。

### `RequestProject/Numerics/Interpolation.lean` —— 多项式插值
* `exists_unique_interpolate`：给定 `n` 个互异节点和任意函数值，存在**唯一**次数 `< n` 的插值多项式。
* `linInterp_error_le`：Lipschitz 函数线性插值的误差界 `|f(x) - L(x)| ≤ L (b - a)`。

### `RequestProject/Numerics/Quadrature.lean` —— 数值积分
* `integral_linInterp`：线性插值多项式的精确积分即梯形公式。
* `trapezoid_exact_affine` / `midpoint_exact_affine`：梯形公式、中矩形公式对一次函数精确
  （代数精度 ≥ 1）。
* `trapezoid_error_le`：梯形公式误差 `≤ L (b - a)²`（`L` 为被积函数的 Lipschitz 常数）。
* `compTrapezoid_error_le`：**复化梯形公式**误差 `≤ L (b - a)² / n`，
  即步长趋于零时数值积分收敛（证明中把积分按子区间分解并逐段估计）。

### `RequestProject/Numerics/Differentiation.lean` —— 数值微分
* `forward_difference_error_le`：前向差商的截断误差 `|(f(x+h) - f(x))/h - f'(x)| ≤ L h / 2`
  （`L` 为 `f'` 的 Lipschitz 常数），即差商是**一阶精度**的。

### `RequestProject/Numerics/ODE.lean` —— 常微分方程数值解
* `discrete_gronwall` / `discrete_gronwall_closed`：**离散 Grönwall 不等式**，
  误差递推 `eₙ₊₁ ≤ a eₙ + d` 的解 `eₙ ≤ aⁿ e₀ + d (aⁿ - 1)/(a - 1)`。
* `euler_global_error_le`：显式 Euler 法的**整体误差界**
  `|yₙ - Y(tₙ)| ≤ τ ((1 + hL)ⁿ - 1)/(hL)`，其中 `τ` 为单步（局部截断）误差界、
  `L` 为右端函数关于 `y` 的 Lipschitz 常数。这正是"局部误差 + 稳定性 ⇒ 收敛"的严格表述。

### `RequestProject/Numerics/FloatingPoint.lean` —— 舍入误差分析
* 采用标准舍入模型 `|rnd(t) - t| ≤ u |t|`（`u` 为机器精度）。
* `sum_forward_error_le`：逐项累加求和的**前向误差界**
  `|ŝₙ - ∑ xᵢ| ≤ ((1 + u)ⁿ - 1) ∑ |xᵢ|`（经典 Wilkinson 型估计）。
* `sum_exact_of_no_rounding`：`u = 0` 时求和精确。

### `RequestProject/Numerics/LinearSystems.lean` —— 数值线性代数
* `relative_error_le_cond`：**条件数**控制解的相对误差
  `‖x - x'‖/‖x‖ ≤ κ(A) · ‖b - b'‖/‖b‖`，`κ(A) = ‖A‖ ‖A⁻¹‖`；这是"病态问题"的严格定义。
* `one_le_cond`：`κ(A) ≥ 1`。
* `det_ne_zero_of_strictlyDiagonallyDominant`（Levy–Desplanques 定理）与
  `isUnit_det_of_strictlyDiagonallyDominant`：严格对角占优矩阵非奇异，
  这是直接法与迭代法中最常用的可解性判据之一。

### `RequestProject/Numerics/Horner.lean` —— 算法正确性
* `horner_eq_sum` / `horner_eq_eval`：Horner（秦九韶）嵌套乘法算法计算的结果
  确实等于多项式 `∑ cᵢ xⁱ` 的值。

---

## 说明与边界

* 上面所有误差界都是**严格证明**的不等式，常数取的是证明中自然得到的值；
  个别地方（如线性插值 `L(b-a)`、梯形公式 `L(b-a)²`）不是教科书中最优的常数，
  但都是无条件成立的正确界。
* 关于光滑函数的经典最优常数（如梯形公式的 `M₂ (b-a)³/12`）同样可以形式化，
  只是需要额外的二阶 Taylor 余项工具；本项目采用了 Lipschitz 假设下的版本。
* 浮点部分用的是**抽象舍入模型**而非 IEEE-754 的位级语义；后者也可以形式化，
  但需要先建立浮点数格式与舍入模式的模型。
* 与"具体程序实现"的连接（编译到机器码后误差界仍成立）属于程序验证范畴，本项目未涉及。
