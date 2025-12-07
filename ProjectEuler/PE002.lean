-- https://projecteuler.net/problem=2
def max : Nat := 4000000

def even_fib_below (max : Nat) :=
  (fib 1 1)
  where fib (a b : Nat) : Nat :=
     (if 2 ∣ a then a else 0) + if a > 0 ∧ b < max then fib (b) (a + b) else 0
  termination_by max - b
  decreasing_by {
    rename_i h
    have ha := h.left
    have hb := h.right
    simp_wf
    apply Nat.sub_lt_sub_left
    · exact hb
    · rw [Nat.add_comm a b] 
      apply Nat.lt_add_of_pos_right
      exact ha
  }

#eval even_fib_below max
