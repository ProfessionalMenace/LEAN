-- Addition is Commutative 
-- Nat.add_comm
example {a b : Nat} : a + b = b + a := by
  induction a with
  | zero => rw [Nat.add_zero, Nat.zero_add]
  | succ n ih =>
    rw [← Nat.succ_eq_add_one]
    rw [Nat.succ_add]
    rw [Nat.add_succ]
    rw [ih]

-- Addition is Associative
-- Nat.add_assoc
example {a b c : Nat} : (a + b) + c = a + (b + c) := by
  induction b with
  | zero => rw [Nat.add_zero, Nat.zero_add]
  | succ n ih => 
    rw [← Nat.succ_eq_add_one]
    rw [Nat.add_succ]
    rw [Nat.succ_add]
    rw [Nat.succ_add]
    rw [Nat.add_succ]
    rw [ih]

-- Unique Predecesor
-- TODO Add uniqness
example (a : Nat) : a ≠ 0 → ∃ (b : Nat), a = b + 1 := by
  intro ha
  cases a with
  | zero => contradiction
  | succ n =>
    constructor
    · rfl

-- Order is Reflexive 
-- Nat.le_refl
example (a : Nat) : a ≤ a := by
  rw [Nat.le_iff_lt_or_eq]
  right
  rfl

-- Order is Transitive
-- Nat.le_trans
example (a b c: Nat) : (b ≤ a) ∧ (c ≤ b) → (c ≤ a) := by
  rintro ⟨hba, hcb⟩
  induction hba with
  | refl => exact hcb 
  | step h h2 =>
      apply Nat.le_succ_of_le
      exact h2

-- Order is Anti-Symmetric
-- Nat.le_antisymm
example (a b : Nat) : (b ≤ a) ∧ (a ≤ b) → (a = b) := by
  rintro ⟨hba, hab⟩
  rw [Nat.le_iff_lt_or_eq] at hba
  rw [Nat.le_iff_lt_or_eq] at hab
  cases hba with
  | inl h1 => cases hab with
    | inl h2 => 
      have h3 := Nat.lt_trans h1 h2
      exact (Nat.lt_irrefl b h3).elim
    | inr h2 => exact h2
  | inr h1 => cases hab with
    | inl h2 => symm; exact h1 
    | inr h2 => exact h2

-- Addition Preserves Order
-- Nat.lt_add_right
example (a b c : Nat) : (a ≤ b) ↔ (a + c ≤ b + c) := by
  induction c with
    | zero =>
      repeat rw [Nat.add_zero]
    | succ n h =>
      repeat rw [Nat.add_succ]
      rw [Nat.succ_le_succ_iff]
      exact h

-- TODO Add more problems and solve them
example (a b : Nat) : a < b ↔ a.succ ≤ b := by
  sorry
