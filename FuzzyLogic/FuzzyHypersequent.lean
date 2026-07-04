/-
Hypersequent calculi for fuzzy logics: BL (Basic Logic) and
Łukasiewicz logic.

`FuzzyFormula` extends the propositional vocabulary with a *fusion*
connective (strong conjunction / t-norm) alongside the lattice meet
(`and`). The residuated implication `imp` is the adjoint of `fusion`.

`HBL` is the hypersequent calculus for BL, obtained from the
HLJ⁰-style base by:
  1. Replacing `Formula` with `FuzzyFormula` (adding `fusion`).
  2. Adding left/right rules for `fusion`.
  3. Adding the communication rule `(com)`.

`HLuk` extends `HBL` with the density rule, yielding a hypersequent
calculus for Łukasiewicz logic.

Reference: Metcalfe, Olivetti, Gabbay, *Proof Theory for Fuzzy Logics*
(Springer, 2009), Ch. 4–5.
-/

namespace HypersequentCalculus

-- ============================================================
--  Syntax
-- ============================================================

/-- Formulas of fuzzy logics over a countable set of atoms.

Compared to `Formula` (the propositional fragment), this type adds
`fusion` (strong conjunction / monoidal tensor) alongside the lattice
`and` (weak conjunction / meet). -/
inductive FuzzyFormula : Type where
  /-- A propositional atom `p₀, p₁, …`. -/
  | atom : Nat → FuzzyFormula
  /-- The absurdity constant `⊥`. -/
  | falsum : FuzzyFormula
  /-- Weak conjunction (lattice meet) `φ ∧ ψ`. -/
  | and : FuzzyFormula → FuzzyFormula → FuzzyFormula
  /-- Strong conjunction (t-norm / monoidal tensor) `φ ⊗ ψ`. -/
  | fusion : FuzzyFormula → FuzzyFormula → FuzzyFormula
  /-- Residuated implication `φ → ψ`. -/
  | imp : FuzzyFormula → FuzzyFormula → FuzzyFormula
  /-- Disjunction (lattice join) `φ ∨ ψ`. -/
  | or : FuzzyFormula → FuzzyFormula → FuzzyFormula
  deriving DecidableEq, Repr

/-- A sequent `Γ ⟹ Δ` in the fuzzy-logic fragment. -/
structure FuzzySequent where
  /-- The antecedent `Γ`. -/
  ante : List FuzzyFormula
  /-- The succedent `Δ`. -/
  succ : List FuzzyFormula
  deriving DecidableEq, Repr

/-- A hypersequent is a finite list of fuzzy sequents. -/
abbrev FuzzyHypersequent := List FuzzySequent

-- ============================================================
--  HBL — Hypersequent calculus for Basic Logic
-- ============================================================

/-- The hypersequent calculus `HBL` for BL (Basic Logic).

`HBL G` means the fuzzy hypersequent `G` is derivable. The system
comprises:
  * Identity and absurdity axioms;
  * External structural rules (weakening, contraction, exchange);
  * Internal structural rules (weakening, contraction);
  * Cut;
  * Logical rules for `∧`, `∨`, `→` (as in HLJ⁰);
  * Fusion rules (`⊗-L`, `⊗-R`);
  * The communication rule `(com)`. -/
inductive HBL : FuzzyHypersequent → Prop where

  /- ---- Axioms ---- -/

  /-- `(Id)` `φ ⟹ φ`. -/
  | id (φ : FuzzyFormula) :
      HBL [⟨[φ], [φ]⟩]

  /-- `(Bot)` `⊥ ⟹ φ`. -/
  | botL (φ : FuzzyFormula) :
      HBL [⟨[.falsum], [φ]⟩]

  /- ---- External structural rules ---- -/

  /-- `(ew)` External weakening. -/
  | ew (S : FuzzySequent) {G : FuzzyHypersequent} :
      HBL G → HBL (S :: G)

  /-- `(ec)` External contraction. -/
  | ec {S : FuzzySequent} {G : FuzzyHypersequent} :
      HBL (S :: S :: G) → HBL (S :: G)

  /-- `(ee)` External exchange: swap adjacent components. -/
  | ee (G : FuzzyHypersequent) {S T : FuzzySequent} {H : FuzzyHypersequent} :
      HBL (G ++ S :: T :: H) → HBL (G ++ T :: S :: H)

  /- ---- Internal structural rules ---- -/

  /-- `(iw-L)` Internal weakening (left). -/
  | iwL (φ : FuzzyFormula) {Γ Δ : List FuzzyFormula} {G : FuzzyHypersequent} :
      HBL (⟨Γ, Δ⟩ :: G) → HBL (⟨φ :: Γ, Δ⟩ :: G)

  /-- `(iw-R)` Internal weakening (right). -/
  | iwR (ψ : FuzzyFormula) {Γ Δ : List FuzzyFormula} {G : FuzzyHypersequent} :
      HBL (⟨Γ, Δ⟩ :: G) → HBL (⟨Γ, ψ :: Δ⟩ :: G)

  /-- `(ic-L)` Internal contraction (left). -/
  | icL {φ : FuzzyFormula} {Γ Δ : List FuzzyFormula} {G : FuzzyHypersequent} :
      HBL (⟨φ :: φ :: Γ, Δ⟩ :: G) → HBL (⟨φ :: Γ, Δ⟩ :: G)

  /-- `(ic-R)` Internal contraction (right). -/
  | icR {ψ : FuzzyFormula} {Γ Δ : List FuzzyFormula} {G : FuzzyHypersequent} :
      HBL (⟨Γ, ψ :: ψ :: Δ⟩ :: G) → HBL (⟨Γ, ψ :: Δ⟩ :: G)

  /- ---- Cut ---- -/

  /-- `(cut)` Cut on formula `δ`. -/
  | cut {Γ₀ Γ₁ Δ₀ Δ₁ : List FuzzyFormula} {δ : FuzzyFormula}
        {G : FuzzyHypersequent} :
      HBL (⟨Γ₀, δ :: Δ₀⟩ :: G) →
      HBL (⟨δ :: Γ₁, Δ₁⟩ :: G) →
      HBL (⟨Γ₀ ++ Γ₁, Δ₀ ++ Δ₁⟩ :: G)

  /- ---- Logical rules: ∧ (weak conjunction / lattice meet) ---- -/

  /-- `(∧₁-L)`. -/
  | andL₁ {φ₁ φ₂ : FuzzyFormula} {Γ Δ : List FuzzyFormula}
          {G : FuzzyHypersequent} :
      HBL (⟨φ₁ :: Γ, Δ⟩ :: G) → HBL (⟨.and φ₁ φ₂ :: Γ, Δ⟩ :: G)

  /-- `(∧₂-L)`. -/
  | andL₂ {φ₁ φ₂ : FuzzyFormula} {Γ Δ : List FuzzyFormula}
          {G : FuzzyHypersequent} :
      HBL (⟨φ₂ :: Γ, Δ⟩ :: G) → HBL (⟨.and φ₁ φ₂ :: Γ, Δ⟩ :: G)

  /-- `(∧-R)`. -/
  | andR {φ₁ φ₂ : FuzzyFormula} {Γ Δ : List FuzzyFormula}
         {G : FuzzyHypersequent} :
      HBL (⟨Γ, φ₁ :: Δ⟩ :: G) →
      HBL (⟨Γ, φ₂ :: Δ⟩ :: G) →
      HBL (⟨Γ, .and φ₁ φ₂ :: Δ⟩ :: G)

  /- ---- Logical rules: ∨ ---- -/

  /-- `(∨-L)`. -/
  | orL {φ₁ φ₂ : FuzzyFormula} {Γ Δ : List FuzzyFormula}
        {G : FuzzyHypersequent} :
      HBL (⟨φ₁ :: Γ, Δ⟩ :: G) →
      HBL (⟨φ₂ :: Γ, Δ⟩ :: G) →
      HBL (⟨.or φ₁ φ₂ :: Γ, Δ⟩ :: G)

  /-- `(∨₁-R)`. -/
  | orR₁ {φ₁ φ₂ : FuzzyFormula} {Γ Δ : List FuzzyFormula}
         {G : FuzzyHypersequent} :
      HBL (⟨Γ, φ₁ :: Δ⟩ :: G) → HBL (⟨Γ, .or φ₁ φ₂ :: Δ⟩ :: G)

  /-- `(∨₂-R)`. -/
  | orR₂ {φ₁ φ₂ : FuzzyFormula} {Γ Δ : List FuzzyFormula}
         {G : FuzzyHypersequent} :
      HBL (⟨Γ, φ₂ :: Δ⟩ :: G) → HBL (⟨Γ, .or φ₁ φ₂ :: Δ⟩ :: G)

  /- ---- Logical rules: → (residuated implication) ---- -/

  /-- `(→-L)`. -/
  | impL {φ ψ : FuzzyFormula} {Γ Δ : List FuzzyFormula}
         {G : FuzzyHypersequent} :
      HBL (⟨Γ, φ :: Δ⟩ :: G) →
      HBL (⟨ψ :: Γ, Δ⟩ :: G) →
      HBL (⟨.imp φ ψ :: Γ, Δ⟩ :: G)

  /-- `(→-R)` Implication-right, restricted to single conclusion
  (as in HLJ⁰). -/
  | impR {φ ψ : FuzzyFormula} {Γ : List FuzzyFormula}
         {G : FuzzyHypersequent} :
      HBL (⟨φ :: Γ, [ψ]⟩ :: G) → HBL (⟨Γ, [.imp φ ψ]⟩ :: G)

  /- ---- Fusion rules (strong conjunction / t-norm) ---- -/

  /-- `(⊗-L)` Fusion left: `φ ⊗ ψ` decomposes to `φ, ψ` in the
  antecedent. -/
  | fusionL {φ ψ : FuzzyFormula} {Γ Δ : List FuzzyFormula}
            {G : FuzzyHypersequent} :
      HBL (⟨φ :: ψ :: Γ, Δ⟩ :: G) → HBL (⟨.fusion φ ψ :: Γ, Δ⟩ :: G)

  /-- `(⊗-R)` Fusion right: derives `φ ⊗ ψ` by splitting the context
  multiplicatively. -/
  | fusionR {φ ψ : FuzzyFormula} {Γ₁ Γ₂ Δ₁ Δ₂ : List FuzzyFormula}
            {G : FuzzyHypersequent} :
      HBL (⟨Γ₁, φ :: Δ₁⟩ :: G) →
      HBL (⟨Γ₂, ψ :: Δ₂⟩ :: G) →
      HBL (⟨Γ₁ ++ Γ₂, .fusion φ ψ :: Δ₁ ++ Δ₂⟩ :: G)

  /- ---- Communication rule ---- -/

  /-- `(com)` The communication rule, characteristic of BL.
  From two components `Γ, Δ ⟹ Θ` and `Γ', Δ' ⟹ Θ'`, produce the
  hypersequent with swapped contexts `Γ, Δ' ⟹ Θ | Γ', Δ ⟹ Θ'`. -/
  | com {Γ Δ Θ Γ' Δ' Θ' : List FuzzyFormula} {G : FuzzyHypersequent} :
      HBL (⟨Γ ++ Δ, Θ⟩ :: G) →
      HBL (⟨Γ' ++ Δ', Θ'⟩ :: G) →
      HBL (⟨Γ ++ Δ', Θ⟩ :: ⟨Γ' ++ Δ, Θ'⟩ :: G)

-- ============================================================
--  HLuk — Hypersequent calculus for Łukasiewicz logic
-- ============================================================

/-- The hypersequent calculus `HŁuk` for Łukasiewicz logic.

`HLuk` extends `HBL` with the density rule (also known as the
splitting rule). Rather than duplicating all constructors of `HBL`,
we embed `HBL` via `ofBL`. -/
inductive HLuk : FuzzyHypersequent → Prop where

  /-- Embed any `HBL` derivation into `HLuk`. -/
  | ofBL {G : FuzzyHypersequent} :
      HBL G → HLuk G

  /-- `(density)` The density (splitting) rule: from a single component
  whose context is a join of two contexts, produce a two-component
  hypersequent. This rule corresponds algebraically to the density
  axiom `(φ → ψ) ∨ (ψ → φ)` being valid in every MV-algebra. -/
  | density {Γ Δ Γ' Δ' : List FuzzyFormula} {G : FuzzyHypersequent} :
      HLuk (⟨Γ ++ Γ', Δ ++ Δ'⟩ :: G) →
      HLuk (⟨Γ, Δ⟩ :: ⟨Γ', Δ'⟩ :: G)

-- ============================================================
--  Worked examples
-- ============================================================

/-- Identity: `⟹ φ → φ` in HBL. -/
example (φ : FuzzyFormula) : HBL [⟨[], [.imp φ φ]⟩] :=
  HBL.impR (HBL.id φ)

/-- Identity lifted to HLuk via embedding. -/
example (φ : FuzzyFormula) : HLuk [⟨[], [.imp φ φ]⟩] :=
  HLuk.ofBL (HBL.impR (HBL.id φ))

/-- Fusion associativity direction: `φ, ψ ⟹ φ ⊗ ψ` in HBL.

Proof sketch:
```
   φ ⟹ φ  (Id)     ψ ⟹ ψ  (Id)
   ─────────────────────────────  (⊗-R)
        φ, ψ ⟹ φ ⊗ ψ
```
-/
example (φ ψ : FuzzyFormula) : HBL [⟨[φ, ψ], [.fusion φ ψ]⟩] :=
  HBL.fusionR (G := []) (Δ₁ := []) (Δ₂ := [])
    (HBL.id φ) (HBL.id ψ)

/-- Fusion-left unfolds: `φ ⊗ ψ, Γ ⟹ Δ` whenever `φ, ψ, Γ ⟹ Δ`.
Here: `φ ⊗ ψ ⟹ φ ⊗ ψ` from `φ, ψ ⟹ φ ⊗ ψ`. -/
example (φ ψ : FuzzyFormula) : HBL [⟨[.fusion φ ψ], [.fusion φ ψ]⟩] :=
  HBL.fusionL
    (HBL.fusionR (G := []) (Δ₁ := []) (Δ₂ := [])
      (HBL.id φ) (HBL.id ψ))

end HypersequentCalculus
