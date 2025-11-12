-- Chapter 4 Quantifiers and Equality
-- https://leanprover.github.io/theorem_proving_in_lean4/Quantifiers-and-Equality/
open Classical

-- Excercise 1
example {α : Type} {r : Prop} : (∃ _ : α, r) → r :=
  (fun her => Exists.elim her (fun _ hr => hr))

-- Excercise 2
example {α : Type} {r : Prop} (a : α) : r → (∃ _ : α, r) := 
  (fun hr => Exists.intro a hr)

-- Excercise 3
example {α : Type} {p : α → Prop} {r : Prop} : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun h => And.intro
      (Exists.elim h (fun ha f => Exists.intro ha f.left))
      (Exists.elim h (fun  _ f => f.right)))
    (fun h => Exists.elim h.left (fun ha hp => Exists.intro ha ⟨hp, h.right⟩))

-- Excercise 4
example {α : Type} {p q : α → Prop} : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun h => Exists.elim h (fun ha h1 => h1.elim
      (fun hpa => Or.inl (Exists.intro ha hpa))
      (fun hqa => Or.inr (Exists.intro ha hqa))))
    (fun h => Or.elim h
      (fun f => Exists.elim f (fun ha hp => Exists.intro ha (Or.inl hp)))
      (fun f => Exists.elim f (fun ha hq => Exists.intro ha (Or.inr hq))))

-- Excercise 5
example {α : Type} {p : α → Prop} : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h1 h2 => Exists.elim h2 (fun ha hnp => hnp (h1 ha)))
    (fun h ha => byContradiction (fun hnp => h (Exists.intro ha hnp)))

-- Excercise 6
example {α : Type} {p : α → Prop} : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun hep hanp => Exists.elim hep (fun ha => hanp ha))
    (fun hnanp => byContradiction (fun hnep => hnanp (fun ha hp => hnep (Exists.intro ha hp))))

-- Excercise 7
example {α : Type} {p : α → Prop} : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (fun hnp ha hp => hnp (Exists.intro ha hp))
  (fun hanp hep => Exists.elim hep (fun ha hpa => absurd hpa (hanp ha)))

-- Excercise 8
example {α : Type} {p : α → Prop} : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h1 => byContradiction (fun h2 => h1 (fun ha => byContradiction (fun hnp => h2 (Exists.intro ha hnp)))))
    (fun h1 h2 => (Exists.elim h1 (fun ha hnp => hnp (h2 ha))))

-- Excercise 9
example {α : Type} {p : α → Prop} {r : Prop} : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h h2 => (Exists.elim h2 (fun ha hp => h ha hp)))
    (fun h ha hp => h (Exists.intro ha hp))

-- Excercise 10
example {α : Type} {p : α → Prop} {r : Prop} {a : α} : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
  (fun h hap => h.elim (fun ha h3 => h3 (hap ha)))
  (fun h => Or.elim (em (∀ (x : α), p x))
    (fun hap => Exists.intro a (fun _ => h hap))
    (fun hnap => byContradiction
      (fun f => hnap
        (fun ha => byContradiction
          (fun hnp => f
            (Exists.intro ha
              (fun hp => absurd hp hnp)))))))

-- Excercise 11
example {α : Type} {p : α → Prop} {r : Prop} {a : α} : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
  (fun he hr => Exists.elim he
    (fun ha hrp => Exists.intro ha (hrp hr)))
  (fun h => Or.elim (em r)
    (fun hr => Exists.elim (h hr)
      (fun ha hp => Exists.intro ha (fun _ => hp)))
    (fun hnr => Exists.intro a (fun hr => absurd hr hnr)))

-- Excercise 12
example {α : Type} {p q : α → Prop} : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (fun h => And.intro
    (fun ha => (h ha).left)
    (fun ha => (h ha).right))
  (fun h ha => ⟨h.left ha, h.right ha⟩)

-- Excercise 13
example {α : Type} {p q : α → Prop} : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  (fun hapq hp ha => hapq ha (hp ha))

-- Excercise 14
example {α : Type} {p q : α → Prop} : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (fun h ha => Or.elim h
    (fun hap => Or.inl (hap ha))
    (fun haq => Or.inr (haq ha)))

-- Excercise 15
example {α : Type} {r : Prop} : α → ((∀ _ : α, r) ↔ r) :=
  (fun ha => Iff.intro
    (fun har => har ha)
    (fun hr _ => hr))

-- Excercise 16
example {α : Type} {r : Prop} {p : α → Prop} : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
  (fun h1 => Or.elim (em r)
    (fun hr => Or.inr hr)
    (fun hnr => Or.inl
      (fun ha => Or.elim (h1 ha)
        (fun hp => hp)
        (fun hr => absurd hr hnr))))
  (fun h ha => Or.elim h
    (fun hap => Or.inl (hap ha))
    (fun hr => Or.inr hr))

-- Excercise 17
example {α : Type} {r : Prop} {p : α → Prop} : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
  (fun h hr ha => h ha hr)
  (fun h ha hr => h hr ha)

-- Excercise 18
example {men : Type} {barber : men} {shaves : men → men → Prop} (h : ∀ x : men, shaves barber x ↔ ¬shaves x x) : False :=
  have h1 := h barber
  have h2 := (h1.mpr (fun f => h1.mp f f))
  (h1.mp h2 h2)

-- DEFINITIONS
def even (n : Nat) : Prop :=
  ∃k , 2*k = n

def prime (n : Nat) : Prop :=
  (n > 1) ∧ ∀(p : Nat), ∀(q : Nat), (p * q = n) → (p = 1 ∧ q = n) ∨ (q = 1 ∧ p = n)

def infinitely_many_primes : Prop := 
  ∀(n : Nat), ∃(p : Nat), (n < p) ∧ (prime p)

def Fermat_prime (n : Nat) : Prop :=
  (prime n) ∧ ∃(k : Nat), (2^k - 1 = n)

def infinitely_many_Fermat_primes : Prop :=
  ∀(n : Nat), ∃(p : Nat), (n < p) ∧ (Fermat_prime n)

def goldbach_conjecture : Prop :=
  ∀(n : Nat), ∃(p : Nat), ∃(q : Nat), (n > 2) ∧ (prime p) ∧ (prime q) ∧ (p + q = n)

def Goldbach's_weak_conjecture : Prop := 
  ∀(n : Nat), ∃(p : Nat), ∃(q : Nat), ∃(r : Nat), (n > 5) ∧ ¬(even n) ∧ (p + q + r = n)

def Fermat's_last_theorem : Prop :=
  ¬∀(n : Nat), ∃(a : Nat), ∃(b : Nat), ∃(c : Nat), (a^n + b^n = c^n)

