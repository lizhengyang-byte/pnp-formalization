/-
  Complexity/Basic.lean

  Abstract machine model for complexity classes.

  We deliberately keep the model abstract: a *machine* is a decider together
  with a step counter, and complexity classes constrain that counter by a
  polynomial in the input length. This is enough to state and prove the
  inclusions established below without committing to a particular machine
  model (Turing machines, RAMs, circuits, ...).
-/

namespace Complexity

/-- An input word over the binary alphabet. -/
abbrev Word : Type := List Bool

/-- A language is a set of words, represented by its membership predicate. -/
structure Language where
  /-- `mem x` holds iff `x` belongs to the language. -/
  mem : Word → Prop

/-- Membership notation `x ∈ L` for languages. -/
instance : Membership Word Language := ⟨fun (L : Language) (x : Word) => L.mem x⟩

/-- Monotonicity of `n ^ i` in the exponent, with all parameters explicit. -/
theorem pow_le_pow_exponent {n i j : Nat} (hn : 0 < n) (h : i ≤ j) : n ^ i ≤ n ^ j :=
  Nat.pow_le_pow_right hn h

/-- A decider together with its step counter. -/
structure Machine where
  /-- The decision procedure. -/
  accept : Word → Bool
  /-- Number of steps spent on a given input. -/
  steps : Word → Nat

namespace Machine

/-- `M` accepts `x`. -/
def Accepts (M : Machine) (x : Word) : Prop := M.accept x = true

/-- `M` runs in polynomial time: there are `k, c` such that on every input `x`
the step count is at most `c * (|x| + 1)^k`. -/
def PolyTime (M : Machine) : Prop :=
  ∃ k c : Nat, ∀ x : Word, M.steps x ≤ c * (x.length + 1) ^ k

end Machine

/-- A verifier: given an input and a certificate, it checks the certificate,
and it has its own step counter. -/
structure Verifier where
  /-- `verify x cert` checks whether `cert` is a valid certificate for `x`. -/
  verify : Word → Word → Bool
  /-- Number of steps spent verifying `x` against `cert`. -/
  steps : Word → Word → Nat

namespace Verifier

/-- `V` runs in polynomial time jointly in the input length and the
certificate length. -/
def PolyTime (V : Verifier) : Prop :=
  ∃ k c : Nat, ∀ x cert : Word,
    V.steps x cert ≤ c * (x.length + cert.length + 1) ^ k

end Verifier

/-- `f` is bounded by a polynomial: `f n ≤ c * (n + 1)^k` for some `k, c`. -/
def PolyBounded (f : Nat → Nat) : Prop :=
  ∃ k c : Nat, ∀ n, f n ≤ c * (n + 1) ^ k

/-- The zero function is polynomially bounded. -/
theorem polyBounded_zero : PolyBounded (fun _ => 0) :=
  ⟨0, 0, by intro n; simp⟩

/-- A constant function is polynomially bounded. -/
theorem PolyBounded.const (c₀ : Nat) : PolyBounded (fun _ => c₀) :=
  ⟨0, c₀, by intro n; simp⟩

/-- Arithmetic core of polynomial closure under addition:
two polynomial bounds with exponents `k₁, k₂` collapse into a single bound
with exponent `k₁ + k₂`. -/
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

/-- Polynomial bounds are closed under pointwise addition. -/
theorem PolyBounded.add {f g : Nat → Nat} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f n + g n) := by
  obtain ⟨k₁, c₁, h₁⟩ := hf
  obtain ⟨k₂, c₂, h₂⟩ := hg
  exact ⟨k₁ + k₂, c₁ + c₂, fun n => by
    exact Nat.le_trans (Nat.add_le_add (h₁ n) (h₂ n))
      (poly_add_bound (k₁ := k₁) (k₂ := k₂) (c₁ := c₁) (c₂ := c₂) (n := n))⟩

/-- A polynomial bound on the input alone is also a polynomial bound jointly in
the input and an arbitrary extra string (the certificate). -/
theorem Machine.PolyTime.weaken {M : Machine} (h : M.PolyTime) :
    ∃ k c : Nat, ∀ x cert : Word, M.steps x ≤ c * (x.length + cert.length + 1) ^ k := by
  obtain ⟨k, c, hk⟩ := h
  refine ⟨k, c, ?_⟩
  intro x cert
  have h₁ : M.steps x ≤ c * (x.length + 1) ^ k := hk x
  have h₂ : (x.length + 1) ^ k ≤ (x.length + cert.length + 1) ^ k :=
    Nat.pow_le_pow_left (by omega : x.length + 1 ≤ x.length + cert.length + 1) k
  exact Nat.le_trans h₁ (Nat.mul_le_mul_left c h₂)

end Complexity
