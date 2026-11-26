# P 与 NP 的形式化地基

## ——一个 Lean 4 中可机器验证的复杂性类框架，兼论「P = NP」为何仍然悬而未决

**摘要.** 本文**不**证明 P = NP，也不声称证明。P 与 NP 是否相等是克雷数学研究所七项千禧年大奖难题之一，自 1971 年 Cook 提出该问题以来一直是开放的。本文所做的是另一件可以真正完成的事：在一个抽象的机器模型中形式化定义复杂性类 P 与 NP，并在 Lean 4 中机器检查地证明若干确实成立的基础结论，包括 P ⊆ NP、P 在补运算下封闭、P 在并与交下封闭。全部定理经 `#print axioms` 审计，仅依赖 Lean 内核的 `propext` 与 `Quot.sound`，不含 `sorry`，不含任何自定义公理。论文随后梳理相对化、自然证明、代数化三类已知障碍，说明为什么"证明 P = NP"不是算力或耐心的问题，而是数学本身的边界问题。

---

## 1. 问题的边界：先说不做什么

必须在开头讲清楚，否则整篇文章的定位会被误读。

**P = NP 目前既没有被证明，也没有被反驳。** 这不是"难题待解"的修辞，而是一个精确的事实状态：不存在任何被同行接受的证明，也不存在任何被同行接受的反驳。任何声称在一次对话、一次计算、一个脚本中完成该证明的产物，只可能属于以下三类：

1. 证明中存在 `sorry` 或其他占位符，编译通过但并未证明；
2. 引入了自定义公理，或把结论写进假设，构成循环论证；
3. 定义被做了手脚（例如让 P 与 NP 退化为同一个类，或让"多项式时间"失去约束力），使定理成立但陈述的不是原问题。

这三类都可以被 Lean 的 `#print axioms` 直接检出。因此本文选择的路线是：**把可以证明的部分做到真正可验证，把不能证明的部分说清楚为什么不能。**

---

## 2. 形式化框架

### 2.1 为什么用抽象机器模型

复杂性理论的标准做法是固定一个计算模型（多带图灵机、RAM、布尔电路），再以步数或门数定义资源。形式化时若一上来就构造图灵机的完整转移函数，工作量会迅速膨胀到与结论本身无关的规模，而结论——P ⊆ NP——并不依赖模型的细节。

因此本文采用一个**抽象模型**：机器是一个判定器加上一个步数计数器。

```lean
structure Machine where
  accept : Word → Bool
  steps : Word → Nat
```

其中 `Word := List Bool`，语言 `Language` 由其成员谓词给出：

```lean
structure Language where
  mem : Word → Prop
```

多项式时间被定义为：存在 `k, c`，使任意输入 `x` 上的步数不超过 `c * (|x| + 1)^k`。

```lean
def Machine.PolyTime (M : Machine) : Prop :=
  ∃ k c : Nat, ∀ x : Word, M.steps x ≤ c * (x.length + 1) ^ k
```

验证器独立建模，其步数同时对输入长度与证书长度做多项式约束：

```lean
def Verifier.PolyTime (V : Verifier) : Prop :=
  ∃ k c : Nat, ∀ x cert : Word,
    V.steps x cert ≤ c * (x.length + cert.length + 1) ^ k
```

这一层的取舍是明确的：它**不**声称覆盖图灵机的所有细节（例如带子数、字母表大小、随机访问），但它足以承载"多项式时间可判定"与"多项式时间可验证"这两个概念的全部组合结构，而这正是 P ⊆ NP 的内容。

### 2.2 类的定义

```lean
def InP (L : Language) : Prop :=
  ∃ M : Machine, M.PolyTime ∧ ∀ x : Word, Machine.Accepts M x ↔ x ∈ L
```

`InNP` 采用证书刻画：存在多项式时间验证器 `V` 与多项式长度的证书界 `p`，使 `x ∈ L` 恰好等价于"存在长度不超过 `p(|x|)` 的证书被 `V` 接受"。

```lean
def InNP (L : Language) : Prop :=
  ∃ V : Verifier, V.PolyTime ∧ ∃ p : Nat → Nat, PolyBounded p ∧
    ∀ x : Word, (x ∈ L ↔ ∃ cert : Word, cert.length ≤ p x.length ∧ V.verify x cert = true)
```

---

## 3. 已证结论

以下每一条都在 Lean 4.36.0 中通过机器检查，源码见仓库 `Complexity/` 目录。

### 3.1 多项式界对加法封闭

**命题 1.** 若 `f`、`g` 均为多项式有界，则 `n ↦ f n + g n` 亦为多项式有界。

证明的关键是：两个不同指数的界可以合并为单一指数 `k₁ + k₂`。

\[
c_1 (n+1)^{k_1} + c_2 (n+1)^{k_2} \le (c_1 + c_2)\,(n+1)^{k_1+k_2}
\]

Lean 中的实现：

```lean
theorem poly_add_bound {k₁ k₂ c₁ c₂ n : Nat} :
    c₁ * (n + 1) ^ k₁ + c₂ * (n + 1) ^ k₂ ≤ (c₁ + c₂) * (n + 1) ^ (k₁ + k₂) := by
  have hb₁ : (n + 1) ^ k₁ ≤ (n + 1) ^ (k₁ + k₂) :=
    pow_le_pow_exponent (n := n + 1) (i := k₁) (j := k₁ + k₂) (by omega) (by omega)
  have hb₂ : (n + 1) ^ k₂ ≤ (n + 1) ^ (k₁ + k₂) :=
    pow_le_pow_exponent (n := n + 1) (i := k₂) (j := k₁ + k₂) (by omega) (by omega)
  calc c₁ * (n + 1) ^ k₁ + c₂ * (n + 1) ^ k₂
      ≤ c₁ * (n + 1) ^ (k₁ + k₂) + c₂ * (n + 1) ^ (k₁ + k₂) :=
        Nat.add_le_add (Nat.mul_le_mul_left c₁ hb₁) (Nat.mul_le_mul_left c₂ hb₂)
    _ = (c₁ + c₂) * (n + 1) ^ (k₁ + k₂) := by rw [Nat.add_mul]
```

这条引理是后面并、交封闭的算术基础，本身也是复杂度理论里"多项式时间对有限次串行组合封闭"的标准事实的一个切片。

### 3.2 P ⊆ NP

**定理 2.** 对任意语言 `L`，若 `L ∈ P`，则 `L ∈ NP`。

证明是构造性的，而且只用了 NP 定义中最弱的一面：**判定器本身就是一个忽略证书的验证器**。取空证书作为唯一证书，长度界 `p ≡ 0`，验证步数直接复用判定步数。由于判定步数对 `|x|` 多项式有界，而 `|x| + 1 ≤ |x| + |cert| + 1`，同一指数 `k` 与同一系数 `c` 直接给出联合多项式界。

```lean
theorem P_subset_NP {L : Language} (h : InP L) : InNP L := by
  obtain ⟨M, htime, hdec⟩ := h
  obtain ⟨k, c, hb⟩ := htime.weaken
  refine ⟨⟨fun x _ => M.accept x, fun x _ => M.steps x⟩, ⟨k, c, hb⟩,
    fun _ => 0, polyBounded_zero, ?_⟩
  intro x
  constructor
  · intro hx
    exact ⟨[], by simp, (hdec x).2 hx⟩
  · rintro ⟨cert, _hlen, hv⟩
    exact (hdec x).1 hv
```

值得注意的是这条证明**没有**用到 NP 的"证书可验证"实质——它只说明 P 是 NP 的子集，而不说明分离。这也解释了为什么 P ⊆ NP 是初等结论，而 P ≠ NP 难如登天：前者只需一个构造，后者需要对**所有**可能的算法给出下界。

### 3.3 P 对补、并、交封闭

**定理 3.** 若 `L ∈ P`，则 `L` 的补集 `∈ P`。构造上把判定器的答案取反，步数完全不变，因此多项式界原样保留。

**定理 4.** 若 `L₁, L₂ ∈ P`，则 `L₁ ∪ L₂ ∈ P` 且 `L₁ ∩ L₂ ∈ P`。构造上串行运行两个判定器，步数相加，由命题 1 得到新的多项式界 `k₁ + k₂`、`c₁ + c₂`。

```lean
theorem InP.union {L₁ L₂ : Language} (h₁ : InP L₁) (h₂ : InP L₂) :
    InP (union L₁ L₂) := by
  obtain ⟨M₁, ht₁, hd₁⟩ := h₁
  obtain ⟨M₂, ht₂, hd₂⟩ := h₂
  obtain ⟨k₁, c₁, hb₁⟩ := ht₁
  obtain ⟨k₂, c₂, hb₂⟩ := ht₂
  refine ⟨⟨fun x => M₁.accept x || M₂.accept x,
    fun x => M₁.steps x + M₂.steps x⟩, ⟨k₁ + k₂, c₁ + c₂, ?_⟩, ?_⟩
  · intro x
    exact Nat.le_trans (Nat.add_le_add (hb₁ x) (hb₂ x))
      (poly_add_bound (k₁ := k₁) (k₂ := k₂) (c₁ := c₁) (c₂ := c₂) (n := x.length))
  · intro x
    show (M₁.accept x || M₂.accept x) = true ↔ (x ∈ L₁ ∨ x ∈ L₂)
    rw [Bool.or_eq_true]
    exact or_congr (hd₁ x) (hd₂ x)
```

补运算的封闭性在标准理论中对应「P 对补封闭」，而 NP 是否对补封闭（即 NP = coNP 是否成立）至今未知——这恰好是 P vs NP 问题旁边另一个仍然开放的分离问题。本文的形式化因此也能作为一个对照：同样的机器模型，补封闭在 P 上是一行构造，在 NP 上就无从下手。

### 3.4 P ⊆ EXP 与 P ⊆ coNP

**定理 5.** 若 `L ∈ P`，则 `L ∈ EXP`。

证明只需一步算术：`m ≤ 2 ^ m` 对一切自然数 `m` 成立，于是多项式界 `c * (|x| + 1)^k` 直接落在指数界 `2 ^ (c * (|x| + 1)^k)` 之内，同一个机器与同一个步数计数器同时是指数时间的。

```lean
theorem P_subset_EXP {L : Language} (h : InP L) : InEXP L := by
  obtain ⟨M, htime, hdec⟩ := h
  obtain ⟨k, c, hb⟩ := htime
  refine ⟨M, ⟨k, c, ?_⟩, hdec⟩
  intro x
  have h₁ : M.steps x ≤ c * (x.length + 1) ^ k := hb x
  have h₂ : c * (x.length + 1) ^ k ≤ 2 ^ (c * (x.length + 1) ^ k) :=
    Nat.le_of_lt Nat.lt_two_pow_self
  exact Nat.le_trans h₁ h₂
```

**定理 6.** 若 `L ∈ P`，则 `L ∈ coNP`。由 `P ⊆ NP` 与 `P` 对补封闭复合得到，一行证明。

```lean
theorem P_subset_coNP {L : Language} (h : InP L) : IncoNP L :=
  P_subset_NP (InP.compl h)
```

到这里可以无条件写下 `P ⊆ NP ∩ coNP` 与 `P ⊆ EXP`。必须强调：这些全部是**包含**，不是**分离**。目前能无条件写下的真分离只有 `P ⊊ EXP`（时间层次定理），而它依赖通用模拟与对角线构造，尚未在本库中形式化——这也正说明"包含链很长、分离一步都难"。

### 3.5 定理清单与审计

| 编号 | 定理（Lean 名） | 内容 | 依赖公理 |
|---|---|---|---|
| 1 | `PolyBounded.add` | 多项式界对逐点加法封闭 | propext, Quot.sound |
| 2 | `P_subset_NP` | P ⊆ NP | propext, Quot.sound |
| 3 | `InP.compl` | P 对补封闭 | propext |
| 4 | `InP.union` | P 对并封闭 | propext, Quot.sound |
| 5 | `InP.inter` | P 对交封闭 | propext, Quot.sound |
| 6 | `InP.empty` / `InP.univ` | 空语言与全语言属于 P | propext, Quot.sound |
| 7 | `P_subset_EXP` | P ⊆ EXP | 无 |
| 8 | `InEXP.compl` | EXP 对补封闭 | propext |
| 9 | `P_subset_coNP` | P ⊆ coNP | propext, Quot.sound |

审计命令与真实输出：

```
$ lake env lean Audit.lean
'Complexity.P_subset_NP' depends on axioms: [propext, Quot.sound]
'Complexity.InP.compl' depends on axioms: [propext]
'Complexity.InP.union' depends on axioms: [propext, Quot.sound]
'Complexity.P_subset_EXP' does not depend on any axioms
'Complexity.P_subset_coNP' depends on axioms: [propext, Quot.sound]
```

`propext` 与 `Quot.sound` 是 Lean 内核的标准公理，任何使用命题外延性或商类型的证明都会带上它们，它们与"存在一个 P = NP 的证明"毫无关系。关键在于输出中**没有** `sorryAx`，也**没有**任何本文自定义的公理。

---

## 4. 为什么 P = NP 仍然悬而未决

如果本文停在上面的定理，读者可能会问：既然形式化这么顺，为什么不顺手把 P ≠ NP 也证了？答案不在工程量，而在数学。

### 4.1 相对化障碍

Baker、Gill 与 Solovay（1975）证明：存在相对化于任意 oracle 的世界里 P = NP，也存在 P ≠ NP 的世界。任何只使用"黑箱模拟"技巧的证明——即对 oracle 一视同仁、不分析计算内部结构的证明——都会在两个世界中给出相同结论，因而必然在其中一个世界里出错。这一障碍排除了 1970 年代绝大多数证明策略。

### 4.2 自然证明障碍

Razborov 与 Rudich（1997）针对电路下界证明提出：若一个"自然"的证明性质具备可构造性与广泛性，则它能攻破强伪随机函数，而后者被认为存在。这使得一大类基于组合性质的电路下界方法失效，也解释了为什么从 Razborov–Smolensky 之后，AC⁰、单调电路之外的下界长期停滞。

### 4.3 代数化障碍

Aaronson 与 Wigderson（2008）进一步指出：把证明"代数化"（允许对多项式做低次扩张）同样会遇到构造性的反例世界。相对化、自然证明、代数化三者构成了当前已知的三道主要屏障。

### 4.4 形式化视角的补充

从证明论的角度还有一层：Lean 的可靠性建立在一致性之上。若在 Lean 中真的给出 P = NP 的完整证明，则该证明同时是一个可被独立核对的数学对象——这恰恰是它至今不存在的原因。形式化系统不会凭空产生数学真理，它只会把已有的证明钉死，或把伪造的证明揪出来。**因此"不计资源消耗地证明 P = NP"这句话本身是不成立的：资源不是瓶颈，未知才是。**

---

## 5. 这份形式化的价值

既然没有解决大问题，这些定理有什么用？有三点。

**第一，它给出一个可复用的地基。** 目前 mathlib 对复杂度类的覆盖近乎空白，本文的抽象模型、多项式界引理、补/并/交封闭可以作为一个起点，向上叠加 Cook–Levin 定理、SAT 归约链、层次定理（P $\subsetneq$ EXP 等）的形式化。

**第二，它把"NP 与 coNP"的对照暴露出来。** 在同一个模型里，P 的补封闭是一行证明，NP 的补封闭则无从下手，这个不对称本身就是教学内容。

**第三，它提供了一个诚实的模板。** 关于 P vs NP 的公开讨论里，伪证明的常见形态就是"定义松、结论大"。本文的做法——先把定义固定，再只证能证的——可以作为一个反例检测的标准动作：任何声称证明 P = NP 的材料，先看它的 `#print axioms`。

## 6. 后续可做的事

按难度递增：

1. 形式化 `NP ⊆ EXP`：需要构造穷举证书的判定器，并证明其步数为指数界。
2. 形式化多项式时间归约 `≤p` 及其传递性，证明 NP 对 `≤p` 归约封闭。
3. 形式化一个具体的 NP 完全问题（如 SAT）及其 NP 成员性，作为 Cook–Levin 定理的实例。
4. 形式化时间层次定理，得到 P $\subsetneq$ EXP 这类无条件分离结论。

第 4 项是本文目前能诚实给出的最强分离结果的方向：不是 P ≠ NP，而是 P $\subsetneq$ EXP，后者是已知定理。

## 7. 结论

P = NP 没有被证明，也没有被反驳。本文在这个前提下做了能做的事：在 Lean 4 中建立一个可审计的复杂性类框架，机器检查地证明 P ⊆ NP、P ⊆ EXP、P ⊆ coNP 与 P 的补、并、交封闭，并用 `#print axioms` 证明这些结论不依赖任何可疑假设。对于"用 Lean 证明 P = NP"这一要求，正确的回答不是交付一个带 `sorry` 的文件，而是把边界画清楚：**能证的已经证了，不能证的仍然是千禧年难题。**

---

### 参考方向

- S. Cook, *The Complexity of Theorem-Proving Procedures*, STOC 1971.
- T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP Question*, SIAM J. Comput. 1975.
- A. Razborov, S. Rudich, *Natural Proofs*, JCSS 1997.
- S. Aaronson, A. Wigderson, *Algebrization: A New Barrier in Complexity Theory*, ACM TOCT 2009.
- Lean 4 官方文档与 `leanprover/lean4` 仓库。
