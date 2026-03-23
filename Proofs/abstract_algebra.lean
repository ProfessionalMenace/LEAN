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
  inv : G → G
  right_inverse (a : G) : a  * (inv a) = e
  left_inverse  (a : G) : (inv a) * a  = e

-- Abelian Group
class AbelianGroup (G : Type u) extends Group G where
  mul_comm (a b : G) : a * b = b * a

-- (trivial) unique identity of a Monoid
theorem id_unique {α : Type u} {M : Monoid α} {a b : α} (ha : a = M.e) (hb : b = M.e) : (a = b) := by
 rw [ha, hb]

-- (trivial) commutativity of inverses
theorem inv_comm {α : Type u} {G : Group α} {a: α} : a * G.inv a = G.inv a * a := by
  rw [G.right_inverse, G.left_inverse]

-- (trivial) element is inverse
theorem mul_eq_one_iff_inv {α : Type u} {G : Group α} {a b: α} (h: a * b = G.e) : b = G.inv a := by
  rw [
    ← G.mul_identity (Group.inv a),
    ← h,
    ← G.mul_assoc,
    G.left_inverse,
    G.identity_mul,
  ]

-- unique inverses of a Group
theorem inv_unique {α : Type u} {G : Group α} {a b c: α} (hab : a * b = G.e) (hac : a * c = G.e) : (b = c) := by
  rw [
    ← G.mul_identity b,
    ← hac,
    ← G.mul_assoc,
    mul_eq_one_iff_inv hab,
    G.left_inverse,
    G.identity_mul
  ]

-- double inverse eq itself
theorem double_inv {α : Type u} {G : Group α} {a : α} : G.inv (G.inv a) = a := by
  rw [
    ← G.identity_mul (G.inv (G.inv a)),
    ← G.right_inverse a,
    G.mul_assoc,
    G.right_inverse,
    G.mul_identity
  ]

-- pair multiplication inverses
theorem pair_inverse {α : Type u} {G : Group α} {a b : α} :  G.inv (a * b) = (G.inv b) * (G.inv a) := by
  rw [
    ← G.mul_identity (G.inv b * G.inv a),
    ← G.right_inverse (a * b),
    ← G.mul_assoc,
    ← G.mul_assoc,
    G.mul_assoc (G.inv b),
    G.left_inverse,
    G.mul_identity,
    G.left_inverse,
    G.identity_mul,
  ]

-- Group left cancelation
theorem left_cancel {α : Type u} {G : Group α} {a b c : α} (h : a * b = a * c) : b = c := by
  rw [
    ← G.identity_mul b,
    ← G.identity_mul c,
    ← G.left_inverse a,
    G.mul_assoc _ a b,
    G.mul_assoc _ a c,
    h
  ]

-- Group right cancelation
theorem right_cancel {α : Type u} {G : Group α} {a b c : α} (h : b * a = c * a) : b = c := by
  rw [
    ← G.mul_identity b,
    ← G.mul_identity c,
    ← G.right_inverse a,
    ← G.mul_assoc b a _,
    ← G.mul_assoc c a _,
    h
  ]
