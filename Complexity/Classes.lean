import Complexity.Basic

/-!
  Complexity/Classes.lean

  The classes `P` and `NP` over the abstract machine model of `Complexity.Basic`,
  together with the basic theorems that are actually known:

  * `P ⊆ NP`
  * `P` is closed under complement, union and intersection

  There is **no** theorem in this file asserting `P = NP`; such a proof does not
  exist today, and this library does not pretend otherwise.
-/

namespace Complexity

/-- `L ∈ P` if some polynomial-time machine decides `L`. -/
def InP (L : Language) : Prop :=
  ∃ M : Machine, M.PolyTime ∧ ∀ x : Word, Machine.Accepts M x ↔ x ∈ L

/-- `L ∈ NP` if some polynomial-time verifier accepts exactly the words of `L`
together with a certificate whose length is polynomially bounded. -/
def InNP (L : Language) : Prop :=
  ∃ V : Verifier, V.PolyTime ∧ ∃ p : Nat → Nat, PolyBounded p ∧
    ∀ x : Word, (x ∈ L ↔ ∃ cert : Word, cert.length ≤ p x.length ∧ V.verify x cert = true)

/-- Complement of a language. -/
def compl (L : Language) : Language := ⟨fun x => ¬ x ∈ L⟩

/-- Union of two languages. -/
def union (L₁ L₂ : Language) : Language := ⟨fun x => x ∈ L₁ ∨ x ∈ L₂⟩

/-- Intersection of two languages. -/
def inter (L₁ L₂ : Language) : Language := ⟨fun x => x ∈ L₁ ∧ x ∈ L₂⟩

/-- **P ⊆ NP.** A polynomial-time decider is a polynomial-time verifier that
ignores its certificate; the empty certificate always suffices. -/
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

/-- `P` is closed under complement: swap the accepting and rejecting answers. -/
theorem InP.compl {L : Language} (h : InP L) : InP (compl L) := by
  obtain ⟨M, htime, hdec⟩ := h
  refine ⟨⟨fun x => !M.accept x, M.steps⟩, htime, ?_⟩
  intro x
  have hx : (M.accept x = true) ↔ x ∈ L := hdec x
  show (!M.accept x = true) ↔ (⟨fun y => ¬ y ∈ L⟩ : Language).mem x
  cases hb : M.accept x
  · have hnot : ¬ x ∈ L := by
      intro hL
      have hacc : M.accept x = true := hx.mpr hL
      rw [hb] at hacc
      exact Bool.noConfusion hacc
    simp [hb, hnot]
  · have hyes : x ∈ L := hx.mp hb
    simp [hb, hyes]

/-- `P` is closed under union: run both deciders and accept if either does. -/
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

/-- `P` is closed under intersection: run both deciders and accept if both do. -/
theorem InP.inter {L₁ L₂ : Language} (h₁ : InP L₁) (h₂ : InP L₂) :
    InP (inter L₁ L₂) := by
  obtain ⟨M₁, ht₁, hd₁⟩ := h₁
  obtain ⟨M₂, ht₂, hd₂⟩ := h₂
  obtain ⟨k₁, c₁, hb₁⟩ := ht₁
  obtain ⟨k₂, c₂, hb₂⟩ := ht₂
  refine ⟨⟨fun x => M₁.accept x && M₂.accept x,
    fun x => M₁.steps x + M₂.steps x⟩, ⟨k₁ + k₂, c₁ + c₂, ?_⟩, ?_⟩
  · intro x
    exact Nat.le_trans (Nat.add_le_add (hb₁ x) (hb₂ x))
      (poly_add_bound (k₁ := k₁) (k₂ := k₂) (c₁ := c₁) (c₂ := c₂) (n := x.length))
  · intro x
    show (M₁.accept x && M₂.accept x) = true ↔ (x ∈ L₁ ∧ x ∈ L₂)
    rw [Bool.and_eq_true]
    exact and_congr (hd₁ x) (hd₂ x)

/-- Sanity check: the empty language is in `P`. -/
theorem InP.empty : InP ⟨fun _ => False⟩ :=
  ⟨⟨fun _ => false, fun _ => 0⟩, ⟨0, 0, by intro x; simp⟩, by
    intro x
    show (false = true) ↔ (⟨fun _ => False⟩ : Language).mem x
    simp⟩

/-- Sanity check: the universal language is in `P`. -/
theorem InP.univ : InP ⟨fun _ => True⟩ :=
  ⟨⟨fun _ => true, fun _ => 0⟩, ⟨0, 0, by intro x; simp⟩, by
    intro x
    show (true = true) ↔ (⟨fun _ => True⟩ : Language).mem x
    simp⟩

end Complexity
