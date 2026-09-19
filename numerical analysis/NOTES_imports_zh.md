# 精简 import：各文件的最小可行依赖

原先各文件都写 `import Mathlib`（一次性引入整个 Mathlib）。现在每个文件只引入自己实际用到的模块，
全部内容（定义、引理、定理与证明）未作任何修改，整个项目 `lake build` 通过，无 `sorry`。

## 各文件的 import

| 文件 | import |
| --- | --- |
| `RequestProject/Numerics/Bisection.lean` | `Mathlib.Topology.Order.IntermediateValue`（介值定理）、`Mathlib.Analysis.SpecificLimits.Basic`（几何列极限） |
| `RequestProject/Numerics/FixedPoint.lean` | `Mathlib.Topology.MetricSpace.Contracting`、`Mathlib.Data.Real.Sqrt`、`Mathlib.Analysis.SpecificLimits.Basic` |
| `RequestProject/Numerics/Interpolation.lean` | `Mathlib.Data.Real.Basic`、`Mathlib.LinearAlgebra.Lagrange`、`Mathlib.Tactic.FieldSimp`、`Mathlib.Tactic.Linarith` |
| `RequestProject/Numerics/Quadrature.lean` | `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`、`Mathlib.Tactic.FunProp`、`RequestProject.Numerics.Interpolation` |
| `RequestProject/Numerics/Differentiation.lean` | `Mathlib.Analysis.SpecialFunctions.Integrals.Basic` |
| `RequestProject/Numerics/ODE.lean` | `Mathlib.Algebra.Field.GeomSum`、`Mathlib.Data.Real.Basic`、`Mathlib.Tactic.GCongr`、`Mathlib.Tactic.Linarith`、`Mathlib.Tactic.Ring`、`Mathlib.Tactic.Push` |
| `RequestProject/Numerics/FloatingPoint.lean` | `Mathlib.Algebra.Order.BigOperators.Ring.Finset`、`Mathlib.Data.Real.Basic`、`Mathlib.Tactic.Linarith` |
| `RequestProject/Numerics/LinearSystems.lean` | `Mathlib.Analysis.Normed.Operator.NormedSpace`、`Mathlib.LinearAlgebra.Matrix.ToLinearEquiv`、`Mathlib.Tactic.Linarith` |
| `RequestProject/Numerics/Horner.lean` | `Mathlib.Algebra.Polynomial.Eval.Defs`、`Mathlib.Data.Real.Basic` |
| `RequestProject/OneTimePad.lean` | `Mathlib.Probability.Distributions.Uniform`、`Mathlib.Data.Set.Card`、`Mathlib.Tactic.Group` |
| `RequestProject/RSA.lean` | `Mathlib.Data.ZMod.Basic`、`Mathlib.Tactic.NormNum.Prime`、`Mathlib.FieldTheory.Finite.Basic` |
| `RequestProject/Shamir.lean` | `Mathlib.Probability.Distributions.Uniform`、`Mathlib.Tactic.FieldSimp` |
| `RequestProject/ElGamal.lean` | `RequestProject.OneTimePad`（本来就没有直接引用 Mathlib） |
| `RequestProject/Main.lean` | 仍为 `import Mathlib`：该文件不含任何数学内容，只是一组 `set_option` / `open scoped` 的配置草稿；如需一并精简，可改为 `import Mathlib.Tactic`（已验证可编译）。 |

## 传递依赖规模（模块数，静态统计 import 闭包）

`import Mathlib` 的闭包为 8181 个模块。精简后各文件的闭包：

```
RequestProject.OneTimePad                      2717  (33%)
RequestProject.RSA                             1985  (24%)
RequestProject.Shamir                          2717  (33%)
RequestProject.ElGamal                         2718  (33%)
RequestProject.Numerics.Bisection              1753  (21%)
RequestProject.Numerics.Differentiation        2827  (35%)
RequestProject.Numerics.FixedPoint             1759  (22%)
RequestProject.Numerics.FloatingPoint          1104  (13%)
RequestProject.Numerics.Horner                 1209  (15%)
RequestProject.Numerics.Interpolation          1824  (22%)
RequestProject.Numerics.LinearSystems          2221  (27%)
RequestProject.Numerics.ODE                    1141  (14%)
RequestProject.Numerics.Quadrature             2831  (35%)
```

说明：Mathlib 中的模块本身依赖较深（例如 `Mathlib.Data.Real.Basic` 已经带来上千个模块），
因此这里的数字是在保持证明原样不动的前提下能达到的自然下界量级；
如果还要进一步压缩，需要改写证明以避开某些重量级依赖（例如把实数换成有序域抽象、避开测度论积分等）。
