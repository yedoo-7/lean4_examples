# 密码学可以做形式化证明吗？

**可以。** 密码学是形式化验证应用得比较成熟的领域之一。大致可以分成三个层次：

1. **数学层（数论、代数、概率）**：RSA/ElGamal/椭圆曲线等方案的正确性，本质上是数论与群论命题，
   可以在 Lean/Coq/Isabelle 这类证明助手中完整证明。
2. **方案安全性（game-based / 归约证明）**：把"若存在攻破方案的敌手，则存在解决某困难问题的算法"
   这类归约写成形式化命题。信息论安全（如一次一密、门限秘密共享的完美保密性）可以无条件地证明；
   计算安全则是在"离散对数困难"等假设下的条件式定理。
3. **协议与实现层**：协议交互层面的符号化分析，以及具体实现（常数时间、内存安全、
   与规范一致）的验证。

本项目给出了第 1 层与第 2 层中"信息论安全"部分的**机器验证**示例，全部在 Lean 4 + Mathlib 中
完成，没有 `sorry`、没有额外公理。

## 本项目中已证明的结果

### `RequestProject/OneTimePad.lean` —— 一次一密的完美保密性
密钥、明文、密文空间都是有限群 `G`，加密为 `m * k`（加法/异或版本同时给出）。

* `map_uniform_mul_left` / `map_uniform_add_left`：密钥均匀随机时，密文分布恰为均匀分布。
* `perfect_secrecy` / `perfect_secrecy_add`：任意两个明文产生的密文分布**完全相同**
  （Shannon 完美保密性）。
* `ciphertext_dist_eq_uniform`：对明文的**任意**先验分布，密文分布仍为均匀分布。
* `ncard_keys_eq_one`：给定明文与密文，恰好存在一个密钥与之相符（计数形式的完美保密性）。
* `decrypt_encrypt`：解密的正确性。

### `RequestProject/RSA.lean` —— RSA 的正确性
* `pow_succ_eq_self_of_prime`：`(p-1) ∣ t` 时，在 `ZMod p` 中对**所有** `m`（含 `m = 0`）
  有 `m ^ (1 + t) = m`（RSA 所需形式的费马小定理）。
* `rsa_correct`：设 `p ≠ q` 为素数，`e * d = 1 + k * lcm (p-1, q-1)`，则对 `ZMod (p*q)` 中
  **所有**消息（不要求与模数互素）都有 `(m ^ e) ^ d = m`。证明用中国剩余定理逐分量归约。
  文件末尾附有 `p = 11, q = 13, e = 7, d = 103` 的具体实例。

### `RequestProject/ElGamal.lean` —— Diffie–Hellman / ElGamal / Pedersen
* `dh_agree`：Diffie–Hellman 双方计算出相同的共享密钥。
* `dec_enc`：ElGamal 解密恢复明文。
* `pedersen_perfectly_hiding`：随机盲化因子均匀时，Pedersen 承诺是完美隐藏的
  （由一次一密的引理直接得到）。

### `RequestProject/Shamir.lean` —— Shamir 门限秘密共享（2 门限）
* `reconstruct`：任意两份份额可恢复秘密。
* `share_dist_eq_uniform` / `single_share_perfect_privacy`：单份份额的分布与秘密无关，
  即一份份额不泄露任何信息。

## 说明与边界

* 上述"安全性"结果都是**信息论意义**的（一次一密、Pedersen 隐藏性、秘密共享隐私性），
  它们无需任何计算困难性假设，因此可以被无条件地证明。
* RSA/ElGamal 这里证明的是**正确性**，不是安全性；其安全性依赖于因子分解 / 离散对数等
  困难性假设，形式化时只能写成"在假设 X 下"的条件式定理。
* 需要建模概率多项式时间敌手的 game-based 证明，在证明助手中也可以做，但需要先建立
  相应的敌手与优势（advantage）模型；本项目未涉及这一部分。
