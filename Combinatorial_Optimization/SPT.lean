/-!
# 贪心算法最优性：SPT 规则最小化总完工时间

单机排序问题 `1 || ∑ C_j`。

一台机器、若干个作业，作业的处理时间为非负整数。一个调度就是把这些作业排成一个序列
（即处理时间列表的一个排列）；排在第 `i` 位的作业的完工时刻是前 `i` 个处理时间之和
`C_i = p_1 + ⋯ + p_i`，目标函数是总完工时间 `∑_i C_i`。

主要结果 `SPT.totalCompletion_pairwise_le`：任何按处理时间**升序**排列的调度，其总完工
时间不超过同一作业集合的任意其它调度。这正是 SPT（shortest processing time first）
贪心规则的最优性；`SPT.totalCompletion_mergeSort_le` 是它对排序算法输出的直接推论。

证明用经典的交换论证（exchange argument）：相邻两个作业若逆序则交换后目标函数不增
(`SPT.totalCompletion_swap_le`)，由此可把最小的作业换到最前面
(`SPT.totalCompletion_move_min_head`)，再对剩下的作业归纳。

本文件是自包含的：只用到 Lean 4 核心库（`List.Perm`、`List.mergeSort` 及 `omega`
等核心策略），不依赖 Mathlib。
-/

namespace SPT

/-- 序列 `l` 的总完工时间 `∑_i C_i`。
按位置展开即 `∑_i (n - i + 1) * p_i`：排在第一位的作业的处理时间会被后面所有作业等待。 -/
def totalCompletion : List Nat → Nat
  | [] => 0
  | p :: rest => (rest.length + 1) * p + totalCompletion rest

/-- 序列 `l` 中各作业的完工时刻列表 `C_1, …, C_n`（前缀和）。 -/
def completionTimes : List Nat → List Nat
  | [] => []
  | p :: rest => p :: (completionTimes rest).map (p + ·)

@[simp] theorem completionTimes_length (l : List Nat) :
    (completionTimes l).length = l.length := by
  induction l with
  | nil => simp [completionTimes]
  | cons p rest ih => simp [completionTimes, ih]

private theorem sum_map_add (p : Nat) (l : List Nat) :
    (l.map (p + ·)).sum = l.length * p + l.sum := by
  induction l with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.succ_mul]
      omega

/-- `totalCompletion` 确实是各作业完工时刻之和。 -/
theorem totalCompletion_eq_sum_completionTimes (l : List Nat) :
    totalCompletion l = (completionTimes l).sum := by
  induction l with
  | nil => simp [completionTimes, totalCompletion]
  | cons p rest ih =>
      simp only [completionTimes, totalCompletion, List.sum_cons,
        sum_map_add, completionTimes_length, ih, Nat.succ_mul]
      omega

/-- **交换论证的核心一步**：相邻两个作业若前者处理时间较小，则该顺序不劣。 -/
theorem totalCompletion_swap_le {x y : Nat} (hxy : x ≤ y) (rest : List Nat) :
    totalCompletion (x :: y :: rest) ≤ totalCompletion (y :: x :: rest) := by
  simp only [totalCompletion, List.length_cons, Nat.succ_mul]
  omega

/-- 在队首加入同一个作业保持比较关系（两个调度作业数相同时）。 -/
theorem totalCompletion_cons_le_cons {u v : List Nat} (a : Nat) (hlen : u.length = v.length)
    (h : totalCompletion u ≤ totalCompletion v) :
    totalCompletion (a :: u) ≤ totalCompletion (a :: v) := by
  simp only [totalCompletion, hlen]
  omega

/-- 把一个不大于前缀 `as` 中所有元素的作业 `m` 提到队首，总完工时间不增。 -/
theorem totalCompletion_move_min_head (m : Nat) :
    ∀ (as bs : List Nat), (∀ x ∈ as, m ≤ x) →
      totalCompletion (m :: (as ++ bs)) ≤ totalCompletion (as ++ m :: bs) := by
  intro as
  induction as with
  | nil => intro bs _; simp
  | cons a as ih =>
      intro bs h
      have hma : m ≤ a := h a (by simp)
      have hstep : totalCompletion (m :: a :: (as ++ bs))
          ≤ totalCompletion (a :: m :: (as ++ bs)) :=
        totalCompletion_swap_le hma _
      have hIH : totalCompletion (m :: (as ++ bs)) ≤ totalCompletion (as ++ m :: bs) :=
        ih bs (fun x hx => h x (by simp [hx]))
      have hlen : (m :: (as ++ bs)).length = (as ++ m :: bs).length := by
        simp
        omega
      calc totalCompletion (m :: (a :: as ++ bs))
          ≤ totalCompletion (a :: m :: (as ++ bs)) := by simpa using hstep
        _ ≤ totalCompletion (a :: (as ++ m :: bs)) :=
            totalCompletion_cons_le_cons a hlen hIH
        _ = totalCompletion (a :: as ++ m :: bs) := by simp

/-- **主定理（SPT 规则最优）**：若 `l` 按处理时间升序排列，则对任意与之作业集合相同
（即互为排列）的调度 `l'`，都有 `totalCompletion l ≤ totalCompletion l'`。 -/
theorem totalCompletion_pairwise_le :
    ∀ (l l' : List Nat), l'.Perm l → l.Pairwise (· ≤ ·) →
      totalCompletion l ≤ totalCompletion l' := by
  intro l
  induction l with
  | nil =>
      intro l' hperm _
      simp [hperm.eq_nil]
  | cons m t ih =>
      intro l' hperm hsorted
      have hmt : ∀ x ∈ t, m ≤ x := (List.pairwise_cons.mp hsorted).1
      have hmem : m ∈ l' := hperm.mem_iff.mpr (by simp)
      obtain ⟨as, bs, rfl⟩ := List.append_of_mem hmem
      have hmid : (as ++ m :: bs).Perm (m :: (as ++ bs)) := List.perm_middle
      have hperm' : (as ++ bs).Perm t := (List.perm_cons m).mp (hmid.symm.trans hperm)
      have has : ∀ x ∈ as, m ≤ x := by
        intro x hx
        have hxl : x ∈ as ++ m :: bs := by simp [hx]
        rcases List.mem_cons.mp (hperm.mem_iff.mp hxl) with h | h
        · omega
        · exact hmt x h
      calc totalCompletion (m :: t)
          ≤ totalCompletion (m :: (as ++ bs)) :=
            totalCompletion_cons_le_cons m hperm'.length_eq.symm
              (ih (as ++ bs) hperm' (List.pairwise_cons.mp hsorted).2)
        _ ≤ totalCompletion (as ++ m :: bs) := totalCompletion_move_min_head m as bs has

/-- 推论：对任意作业列表 `l`，把它按处理时间升序排序（SPT 贪心规则）得到的调度是最优的。 -/
theorem totalCompletion_mergeSort_le (l l' : List Nat) (hperm : l'.Perm l) :
    totalCompletion (l.mergeSort (· ≤ ·)) ≤ totalCompletion l' := by
  refine totalCompletion_pairwise_le _ _
    (hperm.trans (l.mergeSort_perm (· ≤ ·)).symm) ?_
  have htrans : ∀ a b c : Nat, (decide (a ≤ b)) = true → (decide (b ≤ c)) = true →
      (decide (a ≤ c)) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at *
    omega
  have htotal : ∀ a b : Nat, (decide (a ≤ b) || decide (b ≤ a)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  exact (List.pairwise_mergeSort htrans htotal l).imp (by simp)

/-- 调度 `s` 对作业集合 `l` 是**可行的且最优的**：`s` 是 `l` 的一个排列，且它的总完工
时间不超过 `l` 的任何一个排列（即任何一个可行调度）。 -/
def IsOptimalSchedule (l s : List Nat) : Prop :=
  s.Perm l ∧ ∀ t : List Nat, t.Perm l → totalCompletion s ≤ totalCompletion t

/-- **贪心算法的正确性**：对任意作业集合 `l`，按处理时间升序排序得到的调度
（SPT 规则的输出）是这个组合优化问题的一个最优解。 -/
theorem mergeSort_isOptimalSchedule (l : List Nat) :
    IsOptimalSchedule l (l.mergeSort (· ≤ ·)) :=
  ⟨l.mergeSort_perm (· ≤ ·), fun t ht => totalCompletion_mergeSort_le l t ht⟩

/-! ### 小例子：三个作业，处理时间 3、1、2 -/

example : completionTimes [1, 2, 3] = [1, 3, 6] := rfl

example : totalCompletion [1, 2, 3] = 10 := rfl

example : totalCompletion [3, 2, 1] = 14 := rfl

end SPT
