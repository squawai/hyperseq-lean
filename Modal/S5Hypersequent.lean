/-
Hypersequent calculus HS5 for the modal logic S5.

S5 is characterised by Kripke frames where the accessibility relation
is an equivalence relation — equivalently, every world sees every
other world. This allows the accessibility relation to be dropped
entirely from the semantics, and the hypersequent calculus captures the
"multiple worlds" aspect through the external structural rules plus
two pairs of modal rules (`boxR`/`boxL` and `diaR`/`diaL`).

Reference: A. Avron, "A constructive analysis of RM",
           Journal of Symbolic Logic 52(4), 1987.
           (The hypersequent framework; S5 modal rules follow the
           standard Restall / Poggiolesi / Lahav pattern.)
-/

namespace HypersequentCalculus

/-! ## Modal formulas -/

/-- Modal propositional formulas: propositional connectives plus `□` and `◇`. -/
inductive ModalFormula : Type where
  /-- A propositional atom `p₀, p₁, …`. -/
  | atom : Nat → ModalFormula
  /-- The absurdity constant `⊥`. -/
  | falsum : ModalFormula
  /-- Conjunction. -/
  | and : ModalFormula → ModalFormula → ModalFormula
  /-- Disjunction. -/
  | or : ModalFormula → ModalFormula → ModalFormula
  /-- Implication. -/
  | imp : ModalFormula → ModalFormula → ModalFormula
  /-- Necessity `□φ`. -/
  | box : ModalFormula → ModalFormula
  /-- Possibility `◇φ`. -/
  | dia : ModalFormula → ModalFormula
  deriving DecidableEq, Repr

namespace ModalFormula

/-- Negation `¬φ := φ → ⊥`. -/
def neg (φ : ModalFormula) : ModalFormula := imp φ falsum

end ModalFormula

/-! ## Modal sequents and hypersequents -/

/-- A modal sequent `Γ ⟹ Δ` (multi-succedent, classical). -/
structure ModalSequent : Type where
  /-- The antecedent `Γ`. -/
  ante : List ModalFormula
  /-- The succedent `Δ`. -/
  succ : List ModalFormula
  deriving DecidableEq, Repr

/-- A modal hypersequent is a list of modal sequents. -/
abbrev ModalHypersequent := List ModalSequent

/-! ## The hypersequent calculus HS5 -/

/-- `HS5 G` asserts that the modal hypersequent `G` is derivable in
the hypersequent calculus for S5.

**Propositional base**: classical (multi-succedent; `impR` is
unrestricted).

**External structural rules**: weakening (`ew`), contraction (`ec`),
exchange (`ee`), plus internal weakening/contraction on both sides.

**Modal rules**: `boxR` / `boxL` / `diaR` / `diaL` encode the S5
accessibility pattern (universal accessibility = transfer between
components of the hypersequent). -/
inductive HS5 : ModalHypersequent → Prop where
  -- ═══════════════════════════════════════════════════
  -- Axioms
  -- ═══════════════════════════════════════════════════
  /-- Identity axiom: `φ ⟹ φ`. -/
  | id (φ : ModalFormula) :
      HS5 [⟨[φ], [φ]⟩]
  /-- ⊥ on the left derives anything. -/
  | botL (φ : ModalFormula) :
      HS5 [⟨[.falsum], [φ]⟩]

  -- ═══════════════════════════════════════════════════
  -- External structural rules
  -- ═══════════════════════════════════════════════════
  /-- External weakening: add a component. -/
  | ew (S : ModalSequent) {G : ModalHypersequent} :
      HS5 G → HS5 (S :: G)
  /-- External contraction: merge two identical components. -/
  | ec {S : ModalSequent} {G : ModalHypersequent} :
      HS5 (S :: S :: G) → HS5 (S :: G)
  /-- External exchange: swap two adjacent components. -/
  | ee (G : ModalHypersequent) {S T : ModalSequent} {H : ModalHypersequent} :
      HS5 (G ++ S :: T :: H) → HS5 (G ++ T :: S :: H)

  -- ═══════════════════════════════════════════════════
  -- Internal structural rules
  -- ═══════════════════════════════════════════════════
  /-- Internal weakening on the left. -/
  | iwL (φ : ModalFormula) {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨Γ, Δ⟩ :: G) → HS5 (⟨φ :: Γ, Δ⟩ :: G)
  /-- Internal weakening on the right. -/
  | iwR (ψ : ModalFormula) {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨Γ, Δ⟩ :: G) → HS5 (⟨Γ, ψ :: Δ⟩ :: G)
  /-- Internal contraction on the left. -/
  | icL {φ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨φ :: φ :: Γ, Δ⟩ :: G) → HS5 (⟨φ :: Γ, Δ⟩ :: G)
  /-- Internal contraction on the right. -/
  | icR {ψ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨Γ, ψ :: ψ :: Δ⟩ :: G) → HS5 (⟨Γ, ψ :: Δ⟩ :: G)

  -- ═══════════════════════════════════════════════════
  -- Logical rules (classical)
  -- ═══════════════════════════════════════════════════
  /-- ∧-left, first conjunct. -/
  | andL₁ {φ₁ φ₂ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨φ₁ :: Γ, Δ⟩ :: G) → HS5 (⟨.and φ₁ φ₂ :: Γ, Δ⟩ :: G)
  /-- ∧-left, second conjunct. -/
  | andL₂ {φ₁ φ₂ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨φ₂ :: Γ, Δ⟩ :: G) → HS5 (⟨.and φ₁ φ₂ :: Γ, Δ⟩ :: G)
  /-- ∧-right. -/
  | andR {φ₁ φ₂ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨Γ, φ₁ :: Δ⟩ :: G) →
      HS5 (⟨Γ, φ₂ :: Δ⟩ :: G) →
      HS5 (⟨Γ, .and φ₁ φ₂ :: Δ⟩ :: G)
  /-- ∨-left. -/
  | orL {φ₁ φ₂ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨φ₁ :: Γ, Δ⟩ :: G) →
      HS5 (⟨φ₂ :: Γ, Δ⟩ :: G) →
      HS5 (⟨.or φ₁ φ₂ :: Γ, Δ⟩ :: G)
  /-- ∨-right, first disjunct. -/
  | orR₁ {φ₁ φ₂ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨Γ, φ₁ :: Δ⟩ :: G) → HS5 (⟨Γ, .or φ₁ φ₂ :: Δ⟩ :: G)
  /-- ∨-right, second disjunct. -/
  | orR₂ {φ₁ φ₂ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨Γ, φ₂ :: Δ⟩ :: G) → HS5 (⟨Γ, .or φ₁ φ₂ :: Δ⟩ :: G)
  /-- →-left. -/
  | impL {φ ψ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨Γ, φ :: Δ⟩ :: G) →
      HS5 (⟨ψ :: Γ, Δ⟩ :: G) →
      HS5 (⟨.imp φ ψ :: Γ, Δ⟩ :: G)
  /-- →-right (classical: no single-succedent restriction). -/
  | impR {φ ψ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨φ :: Γ, ψ :: Δ⟩ :: G) → HS5 (⟨Γ, .imp φ ψ :: Δ⟩ :: G)

  -- ═══════════════════════════════════════════════════
  -- Modal rules for S5
  -- ═══════════════════════════════════════════════════
  /-- □-right: to derive `□φ` in a component, show `φ` in a fresh
      (empty-context) component added to the hypersequent. -/
  | boxR {φ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨[], [φ]⟩ :: ⟨Γ, Δ⟩ :: G) →
      HS5 (⟨Γ, .box φ :: Δ⟩ :: G)
  /-- □-left: `□φ` on the left unfolds to both `φ` and a persistent
      copy of `□φ` in the same component (reflexivity + transitivity). -/
  | boxL {φ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨φ :: .box φ :: Γ, Δ⟩ :: G) →
      HS5 (⟨.box φ :: Γ, Δ⟩ :: G)
  /-- ◇-right: `◇φ` on the right unfolds to `φ` plus a persistent
      copy of `◇φ` (dual of `boxL`). -/
  | diaR {φ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨Γ, φ :: .dia φ :: Δ⟩ :: G) →
      HS5 (⟨Γ, .dia φ :: Δ⟩ :: G)
  /-- ◇-left: to use `◇φ` on the left, move `φ` to a fresh
      (empty-context) component (dual of `boxR`). -/
  | diaL {φ : ModalFormula} {Γ Δ : List ModalFormula} {G : ModalHypersequent} :
      HS5 (⟨[φ], []⟩ :: ⟨Γ, Δ⟩ :: G) →
      HS5 (⟨.dia φ :: Γ, Δ⟩ :: G)

/-! ## S5 Kripke semantics (type stubs) -/

/-- An S5 Kripke model. Since S5 frames have a universal accessibility
relation, we omit it entirely: every world sees every world. -/
structure S5Model where
  /-- The type of worlds. -/
  W : Type
  /-- The valuation: which atoms are true at each world. -/
  val : W → Nat → Prop

/-- Forcing relation for modal formulas on an S5 model. -/
def S5Force (M : S5Model) (w : M.W) : ModalFormula → Prop
  | .atom n     => M.val w n
  | .falsum     => False
  | .and φ ψ    => S5Force M w φ ∧ S5Force M w ψ
  | .or φ ψ     => S5Force M w φ ∨ S5Force M w ψ
  | .imp φ ψ    => S5Force M w φ → S5Force M w ψ
  | .box φ      => ∀ v : M.W, S5Force M v φ
  | .dia φ      => ∃ v : M.W, S5Force M v φ

/-- A modal formula is S5-valid iff it is forced at every world of
every S5 model. -/
def S5Valid (φ : ModalFormula) : Prop :=
  ∀ (M : S5Model) (w : M.W), S5Force M w φ

/-- A modal hypersequent is valid in an S5 model at a world
assignment iff some component is satisfied (ante all forced → some
succ forced). -/
def S5HValid (G : ModalHypersequent) : Prop :=
  ∀ (M : S5Model) (f : Fin G.length → M.W),
    ∃ i : Fin G.length,
      (∀ φ ∈ G[i].ante, S5Force M (f i) φ) →
      (∃ ψ ∈ G[i].succ, S5Force M (f i) ψ)

end HypersequentCalculus
