-- Semigroup
class Semigroup (G : Type u) extends Mul G where
  mul_assoc (a b c : G): (a * b) * c = a * (b * c)

-- Monoid
class Monoid (M : Type u) extends Semigroup M where
  e: M
  identity_mul (a : M) : e * a = a
  mul_identity (a : M) : a * e = a

-- Group
class Group (G : Type u) extends Monoid G where
  right_inverse (a : G) : ∃(b : G), a * b = e
  left_inverse (a : G) : ∃(b : G), b * a = e

-- Abelian Group (todo)
class AbelianGroup (G : Type u) extends Group G where
  mul_comm (a b : G) : a * b = b * a

-- unique identity of a Monoid
theorem id_unique {α : Type u} {M : Monoid α} (a b : α) : (a = M.e) ∧ (b = M.e) → (a = b) := sorry

-- unique inverses of a Group
theorem inv_unique {α : Type u} {G : Group α} (a b c : α) : (a * b = G.e) ∧ (a * c = G.e) → (a = b) := sorry

-- double inverse eq itself
theorem double_inv {α : Type u} {G : Group α} (a : α) :
  ∃(b : α), a * b = G.e
  ∧ ∃(c : α), (a * b) * c = G.e
  → c = a := sorry

-- pair multiplication inverses
theorem pair_inverse {α : Type u} {G : Group α} (a b: α) :
  ∃(a' : α), a * a' = G.e
  ∧ ∃(b' : α), b * b' = G.e
  ∧ ∃(ab' : α), (a * b) * ab' = G.e
  → ab' = b' * a'
  := sorry

-- Group left cancelation
theorem left_cancel {α : Type u} {G : Group α} (a b c : α) : a * b = a * c → b = c := sorry

-- Group right cancelation
theorem right_cancel {α : Type u} {G : Group α} (a b c : α) : b * a = c * a → b = c := sorry
