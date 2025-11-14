-- Chapter 5 Tactics
-- commutativity of ∧
example {p q : Prop} : p ∧ q ↔ q ∧ p := by
  apply Iff.intro 
  rintro ⟨hp, hq⟩; exact ⟨hq, hp⟩
  rintro ⟨hq, hp⟩; exact ⟨hp, hq⟩

-- commutativity of ∨
example {p q: Prop} : p ∨ q ↔ q ∨ p := by
  constructor

  intro pvq
  cases pvq with
  | inl hp => apply Or.inr hp
  | inr hq => apply Or.inl hq

  intro qvp
  cases qvp with
  | inl hq => apply Or.inr hq
  | inr hp => apply Or.inl hp

-- associativity of ∧
example {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  rintro ⟨⟨hp, hq⟩, hr⟩; exact ⟨hp, ⟨hq, hr⟩⟩
  rintro ⟨hp, ⟨hq, hr⟩⟩; exact ⟨⟨hp, hq⟩, hr⟩

-- associativity of ∨
example {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  intro h1
  cases h1 with
  | inl hpq => cases hpq with 
    | inl hp => exact Or.inl hp
    | inr hq => exact Or.inr (Or.inl hq)
  | inr hr => exact Or.inr (Or.inr hr)
  intro h2
  cases h2 with
  | inl hp => exact Or.inl (Or.inl hp)
  | inr hqr => cases hqr with
    | inl hq => exact Or.inl (Or.inr hq)
    | inr hr => exact Or.inr hr

-- distributivity
example {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  rintro ⟨hp, hqvr⟩
  cases hqvr with
  | inl hq => exact Or.inl ⟨hp, hq⟩
  | inr hr => exact Or.inr ⟨hp, hr⟩ 
  intro h2
  cases h2 with
  | inl hpaq => exact ⟨hpaq.left, Or.inl hpaq.right⟩
  | inr hpar => exact ⟨hpar.left, Or.inr hpar.right⟩

-- distributivity
example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor

  intro h1
  cases h1 with
  | inl hp => exact ⟨Or.inl hp, Or.inl hp⟩
  | inr hqvr => exact ⟨Or.inr hqvr.left, Or.inr hqvr.right⟩

  rintro ⟨hpvq, hpvr⟩
  cases hpvq with
  | inl hp => exact Or.inl hp
  | inr hq => cases hpvr with
    | inl hp => exact Or.inl hp
    | inr hr => exact Or.inr ⟨hq, hr⟩

-- other properties 1
example {p q r :  Prop} : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  rintro hr ⟨hp, hq⟩
  exact hr hp hq 
  intro h2 hp hq
  exact h2 ⟨hp, hq⟩

-- other properties 2
example {p q r : Prop} : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  intro h1
  apply And.intro
  intro hp
  exact h1 (Or.inl hp)
  intro hq
  exact h1 (Or.inr hq)
  rintro ⟨hpr, hqr⟩ hpq
  cases hpq with
  | inl hp => exact hpr hp
  | inr hq => exact hqr hq

-- other properties 3
example {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  intro h1
  apply And.intro
  intro hp
  apply h1
  apply Or.inl hp
  intro hq
  apply h1
  apply Or.inr hq
  intro h2 h3
  cases h3 with
  | inl hp => exact h2.left hp
  | inr hq => exact h2.right hq

-- other properties 4
example {p q : Prop} : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h1 h2
  cases h1 with
  | inl hnp => exact hnp h2.left
  | inr hnq => exact hnq h2.right

-- other properties 6
example {p q : Prop} : p ∧ ¬q → ¬(p → q) := by
  intro h1 h2
  apply h1.right
  apply h2
  exact h1.left

-- other properties 7
example {p q : Prop} : ¬p → (p → q) := by
  intro hnp hp
  apply absurd hp hnp

-- other properties 8
example {p q : Prop} : (¬p ∨ q) → (p → q) := by
  intro h hp
  cases h with
  | inl hnp => exact absurd hp hnp
  | inr hq => exact hq

-- other properties 9
example {p : Prop} : p ∨ False ↔ p := by
  apply Iff.intro
  intro h1
  cases h1 with
  | inl hp => exact hp
  | inr hf => exact False.elim hf
  intro hp
  exact Or.inl hp

-- other properties 10
example {p : Prop} : p ∧ False ↔ False := by
  apply Iff.intro
  intro h1
  exact h1.right
  intro h2
  exact False.elim h2

-- other properties 11
example {p q : Prop} : (p → q) → (¬q → ¬p) := by
  intro h hnq hp
  have hq := h hp
  apply absurd hq hnq

open Classical

-- classical 1
example {p q r : Prop} : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h1
  cases em p with
  | inl hp => cases h1 hp with
    | inl hq => apply Or.inl; intro _; exact hq
    | inr hr => apply Or.inr; intro _; exact hr
  | inr hnp => apply Or.inl; intro hp; exact absurd hp hnp

-- classical 2
example {p q : Prop} : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h1
  cases em p with
  | inl hp => apply Or.inr; intro hq; exact h1 ⟨hp, hq⟩
  | inr hnp => apply Or.inl; exact hnp

-- classical 3
example {p q : Prop} : ¬(p → q) → p ∧ ¬q := by
  intro h
  apply And.intro
  cases em p with
  | inl hp => exact hp 
  | inr hnp => apply False.elim; apply h; intro hp; exact absurd hp hnp
  intro hq
  apply h
  intro hp
  exact hq

-- classical 4
example {p q : Prop} : (p → q) → (¬p ∨ q) := by
  intro hpq
  cases em p with
  | inl hp => exact Or.inr (hpq hp)
  | inr hnp => exact Or.inl hnp

-- classical 5
example {p q : Prop} : (¬q → ¬p) → (p → q) := by
  intro h hp
  cases em q with
  | inl hq => exact hq
  | inr hnq => exact absurd hp (h hnq)

-- classical 6
example {p : Prop} : p ∨ ¬p := by
  apply em p

-- classical 7
example {p q : Prop} : (((p → q) → p) → p) := by
  intro h
  cases em p with 
  | inl hp => exact hp
  | inr hnp => apply h; intro hp; exact absurd hp hnp

-- BONUS
example {p : Prop} : ¬(p ↔ ¬p) := by
  rintro ⟨hpnp, hnpp⟩
  apply hpnp
  apply hnpp
  intro hp
  exact hpnp hp hp
  apply hnpp
  intro hp
  apply hpnp hp hp

-- quantifiers 1
example {α : Type} {r : Prop} : (∃ _ : α, r) → r := by
  intro h1
  apply Exists.elim h1
  intro h2 hr
  exact hr

-- quantifiers 2
example {α : Type} {r : Prop} (a : α) : r → (∃ _ : α, r) := by
  intro hr
  apply Exists.intro
  exact hr
  exact a

-- quantifiers 3
example {α : Type} {p : α → Prop} {r : Prop} : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor

  intro h1
  apply Exists.elim h1
  intros hα h2
  apply And.intro
  case left =>  apply Exists.intro; exact h2.left
  case right => exact h2.right

  intro h3
  have h4 := h3.left
  have hr := h3.right
  apply Exists.elim h4
  intro hα h5
  apply Exists.intro
  apply And.intro <;> assumption

-- quantifiers 4
example {α : Type} {p q : α → Prop} : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by 
  apply Iff.intro
  case mp =>
    intro h1
    apply Exists.elim h1
    intro hα h2
    cases h2 with
    | inl f => apply Or.inl; apply Exists.intro; exact f;
    | inr f => apply Or.inr; apply Exists.intro; exact f; 
  case mpr =>
    intro h3
    cases h3 with
    | inl f => apply Exists.elim f; intro hα hp; apply Exists.intro; apply Or.inl hp;
    | inr f => apply Exists.elim f; intro hα hq; apply Exists.intro; apply Or.inr hq;

-- quantifiers 5
example {α : Type} {p : α → Prop} : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor

  intro h1 h2
  apply Exists.elim h2
  intro hα hnp
  have hp := h1 hα 
  apply absurd hp hnp

  intro h1 ha
  apply byContradiction 
  intro hnp
  apply h1
  apply Exists.intro ha hnp 
    
-- quantifiers 6
example {α : Type} {p : α → Prop} : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor

  intro hep hanp
  apply Exists.elim hep
  intro ha hp
  have hnp := hanp ha
  exact absurd hp hnp 

  intro hnanp
  apply byContradiction
  intro hnep
  apply hnanp
  intro ha hp
  apply hnep
  exact Exists.intro ha hp

-- quantifiers 7
example {α : Type} {p : α → Prop} : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor

  intro hnep ha hp
  apply hnep
  exact Exists.intro ha hp

  intro hanp hep
  apply Exists.elim hep
  intro ha hp
  exact hanp ha hp

-- quantifiers 8
example {α : Type} {p : α → Prop} : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor

  intro hnap
  apply byContradiction
  intro hnenp
  apply hnap
  intro ha
  apply byContradiction
  intro hnp
  apply hnenp
  apply Exists.intro ha hnp

  intro henp hap
  apply Exists.elim henp
  intro ha hnp
  have hp := hap ha
  exact absurd hp hnp

-- quantifiers 9
example {α : Type} {p : α → Prop} {r : Prop} : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor

  intro h hep
  apply Exists.elim hep
  intro ha hp
  exact h ha hp

  intro h ha hp
  apply h
  apply Exists.intro ha hp

-- quantifiers 10
example {α : Type} {p : α → Prop} {r : Prop} (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor

  intro h1 h2
  apply Exists.elim h1
  intro ha h3
  apply h3
  exact h2 ha

  intro h1
  cases (em (∀ (x : α), p x)) with
  | inl hap =>
    apply Exists.intro a
    have hr := h1 hap
    intro hp
    exact hr
  | inr hnap =>
    apply byContradiction
    intro h2
    apply hnap
    intro ha
    apply byContradiction
    intro hnp
    apply h2
    apply Exists.intro ha
    intro hp
    apply absurd hp hnp

-- quantifiers 11
example {α : Type} {p : α → Prop} {r : Prop} {a : α} : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor

  rintro ⟨ha, hrp⟩ hr
  have hp := hrp hr
  apply Exists.intro ha hp

  intro h
  cases (em r) with
  | inl hr =>
    have hep := h hr
    apply Exists.elim hep
    intro ha hp
    apply Exists.intro
    case inl.h =>
      intro _
      exact hp
  | inr hnr =>
    apply Exists.intro a
    intro hr
    apply absurd hr hnr

-- quantifiers 12
example {α : Type} {p q : α → Prop} : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor

  intro h1
  apply And.intro
  intro ha
  exact (h1 ha).left
  intro ha
  exact (h1 ha).right

  intro h1 ha
  apply And.intro
  exact (h1.left ha)
  exact (h1.right ha)

-- quantifiers 13
example {α : Type} {p q : α → Prop} : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by 
  intro h1 hap ha
  have hp := (hap ha)
  exact h1 ha hp

-- quantifiers 14
example {α : Type} {p q : α → Prop} : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h1 ha
  cases h1 with
  | inl hap => apply Or.inl; exact hap ha
  | inr haq => apply Or.inr; exact haq ha

-- quantifiers 15
example {α : Type} {r : Prop} : α → ((∀ _ : α, r) ↔ r) := by
  intro ha
  constructor
  intro har; exact har ha
  intro hr _; exact hr

-- quantifiers 16
example {α : Type} {r : Prop} {p : α → Prop} : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor

  intro h1
  cases (em r) with
  | inl hr => apply Or.inr hr
  | inr hnr =>
    apply Or.inl
    intro ha
    cases (h1 ha) with
    | inl hp => exact hp
    | inr hr => exact absurd hr hnr

  intro h1 ha
  cases h1 with
  | inl hap => apply Or.inl; exact hap ha
  | inr hr => apply Or.inr; exact hr

-- quantifiers 18
example {men : Type} {barber : men} {shaves : men → men → Prop} (h : ∀ x : men, shaves barber x ↔ ¬shaves x x) : False := by
  have ⟨hmp, hmpr⟩ := h barber
  apply hmp

  apply hmpr
  intro h2
  apply hmp h2 
  exact h2

  apply hmpr
  intro h3
  apply hmp
  exact h3
  exact h3

