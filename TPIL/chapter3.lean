-- Excercises from book Theorem Proving in Lean 4
-- https://leanprover.github.io/theorem_proving_in_lean4/Propositions-and-Proofs

-- commutativity of ∧
example {p q : Prop} : p ∧ q ↔ q ∧ p := 
  Iff.intro (fun h: p ∧ q => ⟨h.right, h.left⟩) (fun h: q ∧ p => ⟨h.right, h.left⟩)

-- commutativity of ∨
example {p q : Prop} : p ∨ q ↔ q ∨ p := 
  Iff.intro
    (fun hpq: p ∨ q => show q ∨ p from Or.elim hpq
      (fun hp: p => Or.inr hp)
      (fun hq: q => Or.inl hq))
    (fun hqp: q ∨ p => show p ∨ q from Or.elim hqp
      (fun hq: q => Or.inr hq)
      (fun hp: p => Or.inl hp))

-- commutativity of ∨ (Thanks Tenth!!!)
example {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨fun ⟨⟨p, q⟩, r⟩ => ⟨p, ⟨q, r⟩⟩, fun ⟨p, ⟨q, r⟩⟩ => ⟨⟨p, q⟩, r⟩⟩

-- associativity of ∧
example {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h1: (p ∧ q) ∧ r => 
      have hp := h1.left.left
      have hq := h1.left.right
      have hr := h1.right
    show p ∧ (q ∧ r) from And.intro hp (And.intro hq hr))
    (fun h2: p ∧ (q ∧ r) => 
      have hp := h2.left
      have hq := h2.right.left
      have hr := h2.right.right
      show (p ∧ q) ∧ r from And.intro (And.intro hp hq) hr)

-- associativity of ∨
example {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h1: (p ∨ q) ∨ r => show p ∨ (q ∨ r) from Or.elim h1
      (fun hpq: p ∨ q => Or.elim hpq 
        (fun hp: p => Or.inl hp)
        (fun hq: q => Or.inr (Or.inl hq)))
      (fun hr: r => Or.inr (Or.inr hr)))
    (fun h2: p ∨ (q ∨ r) => show (p ∨ q) ∨ r from Or.elim h2
      (fun hp: p => Or.inl (Or.inl hp))
      (fun hqr: q ∨ r => Or.elim hqr
        (fun hq: q => Or.inl (Or.inr hq))
        (fun hr: r => Or.inr hr)))

-- distributivity 1
example {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h1: p ∧ (q ∨ r) => 
      have hp: p := h1.left
      have hqr: q ∨ r := h1.right
      show (p ∧ q) ∨ (p ∧ r) from Or.elim hqr 
        (fun hq: q => Or.inl (And.intro hp hq))
        (fun hr: r => Or.inr (And.intro hp hr)))
    (fun h2: (p ∧ q) ∨ (p ∧ r) => show p ∧ (q ∨ r) from Or.elim h2
      (fun hpq: p ∧ q => And.intro (hpq.left) (Or.inl hpq.right))
      (fun hpr: p ∧ r => And.intro (hpr.left) (Or.inr hpr.right)))

-- distributivity 2
example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h1: p ∨ (q ∧ r) => show (p ∨ q) ∧ (p ∨ r) from Or.elim h1
      (fun hp: p => And.intro (Or.inl hp) (Or.inl hp))
      (fun hqr: q ∧ r => And.intro (Or.inr hqr.left) (Or.inr hqr.right)))
    (fun h2: (p ∨ q) ∧ (p ∨ r) =>
      have hpq: p ∨ q := h2.left
      have hpr: p ∨ r := h2.right
      show p ∨ (q ∧ r) from Or.elim hpq 
        (fun hp: p => Or.inl hp)
        (fun hq: q => Or.elim hpr
          (fun hp: p => Or.inl hp)
          (fun hr: r => Or.inr (And.intro hq hr))))

-- other properties 1
example {p q r : Prop} : (p → (q → r)) ↔ ((p ∧ q) → r) :=
  Iff.intro
    (fun (h1: p → q → r) (hpq: p ∧ q) => h1 hpq.left hpq.right)
    (fun (h2: p ∧ q → r) (hp: p) (hq: q) => h2 (And.intro hp hq))

-- other properties 2
example {p q r : Prop} : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h1: p ∨ q → r => And.intro 
      (fun hp => h1 (Or.inl hp))
      (fun hq => h1 (Or.inr hq)))
    (fun (h1: (p → r) ∧ (q → r)) (hpq: p ∨ q) => Or.elim hpq
      (fun hp => h1.left hp)
      (fun hq => h1.right hq))

-- other properties 3
example {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro
    (fun h => And.intro (fun hp => h (Or.inl hp)) (fun hq => h (Or.inr hq)))
    (fun h1 h2 => Or.elim h2 h1.left h1.right)

-- other properties 4
example {p q : Prop} : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (fun h1 h2 => Or.elim h1
    (fun h3 => absurd h2.left h3)
    (fun h3 => absurd h2.right h3))

-- other properties 5
example {p : Prop} : ¬(p ∧ ¬p) :=
  (fun h => absurd h.left h.right) 

-- other properties 6
example {p q : Prop} : p ∧ ¬q → ¬(p → q) :=
  (fun h1 h2 => absurd (h2 h1.left) h1.right)

-- other properties 7
example {p q : Prop} : ¬p → (p → q) :=
  (fun hnp hp => absurd hp hnp)

-- other properties 8
example {p q : Prop} : (¬p ∨ q) → (p → q) :=
  (fun h hp => Or.elim h
    (fun hnp => absurd hp hnp)
    (fun hq => hq))

-- other properties 9
example {p : Prop} : p ∨ False ↔ p :=
  Iff.intro
    (fun h => Or.elim h
      (fun hp => hp)
      (fun f => False.elim f))
    (fun hp => Or.inl hp)

-- other properties 10
example {p : Prop} : p ∧ False ↔ False :=
  Iff.intro
    (fun h => h.right)
    (fun f => False.elim f)

-- other properties 11
example {p q : Prop} : (p → q) → (¬q → ¬p) :=
  (fun h1 hnq hp => absurd (h1 hp) hnq) 

-- CLASSICAL SECTION
open Classical

-- example 1
example {p q : Prop} : ¬(p ∧ ¬q) → (p → q) :=
  fun (h: ¬(p ∧ ¬q)) (hp: p) => show q from Or.elim (em q)
    (fun hq : q => hq)
    (fun hnq : ¬q => absurd (And.intro hp hnq) h)

-- example 2
example {p q : Prop} (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p => Or.inr (fun hq : q => h ⟨hp, hq⟩))
    (fun hp : ¬p => Or.inl hp)

-- classical 1
example {p q r : Prop} : (p → (q ∨ r)) → ((p → q) ∨ (p → r)) := 
  (fun h => Or.elim (em p)
    (fun hp => Or.elim (h hp)
      (fun hq => Or.inl (fun _ => hq))
      (fun hr => Or.inr (fun _ => hr)))
    (fun hnp => Or.inl (fun hp => absurd hp hnp)))

-- classical 2
example {p q : Prop} : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (fun h => Or.elim (em p)
  (fun hp => Or.elim (em q)
    (fun hq => False.elim (h (And.intro hp hq)))
    (fun hnq => Or.inr hnq))
  (fun hnp => Or.inl hnp))

-- classical 3
example {p q : Prop} : ¬(p → q) → p ∧ ¬q :=
  (fun h => And.intro
    (Or.elim (em p)
      (fun hp => hp)
      (fun hnp => False.elim (h (fun hp => absurd hp hnp))))
    (fun hq => h (fun _ => hq)))

-- classical 4
example {p q : Prop} : (p → q) → (¬p ∨ q) :=
  (fun h => Or.elim (em p)
    (fun hp => Or.inr (h hp))
    (fun hnp => Or.inl hnp))

-- classical 5
example {p q : Prop} : (¬q → ¬p) → (p → q) :=
  (fun h hp => Or.elim (em q)
    (fun hq => hq)
    (fun hnq => absurd (hp) (h hnq)))

-- classical 6
example {p : Prop} : p ∨ ¬p :=
  em p

-- classical 7
example {p q : Prop} : (((p → q) → p) → p) :=
  (fun h: (p → q) → p => show p from Or.elim (em p)
    (fun hp: p => hp)
    (fun hnp: ¬p => h (fun hp => absurd hp hnp)))

-- BONUS!!!
example {p : Prop} : ¬(p ↔ ¬p) := 
  fun h => 
    have f := h.mpr (fun hp => h.mp hp hp)
    h.mp f f

