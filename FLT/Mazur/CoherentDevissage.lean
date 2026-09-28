/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Ingredients for coherent dévissage

This file provides stalk support, Noetherian induction on closed subsets, and
finite extension arguments for properties of locally finitely presented module
sheaves. It does not prove the generic-rank-one criterion of Stacks 01YI.
The missing geometric steps are closedness of coherent support, coherent
subquotients, and extension of generic-point comparisons.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X : Scheme.{u}}

/-- The additive stalk of an actual module sheaf. -/
abbrev stalk (x : X) : X.Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

instance (x : X) : (stalk x).Additive where
  map_add {M N} f g := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (f.mapPresheaf + g.mapPresheaf) = _
    exact Functor.map_add _

/-- Support is the locus of nonzero stalks; no closedness is built into this definition. -/
def support (M : X.Modules) : Set X := {x | ¬ IsZero ((stalk x).obj M)}

/-- Isomorphic sheaves have the same support. -/
lemma support_iso {M N : X.Modules} (e : M ≅ N) : support M = support N := by
  ext x
  exact not_congr ((stalk x).mapIso e).isZero_iff

/-- A zero sheaf has empty support. -/
lemma support_eq_empty_of_isZero {M : X.Modules} (hM : IsZero M) :
    support M = ∅ := by
  ext x
  simp only [support, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact (stalk x).map_isZero hM

/-- The support of a subsheaf is contained in that of the ambient sheaf. -/
lemma support_subset_of_mono {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    support M ⊆ support N := by
  let F : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf X.ringCatSheaf
  have : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))
  intro x hx hN
  exact hx (hN.of_mono ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (F.map f)))

/-- Noetherian induction with an explicit closed support bound. -/
theorem closed_induction [IsNoetherian X] (Q : Closeds X → Prop)
    (step : ∀ Z, (∀ W < Z, Q W) → Q Z) (Z : Closeds X) : Q Z :=
  wellFounded_lt.induction Z step

/-- To prove a property of all closed sets, it suffices to handle irreducible sets
by induction and to preserve the property under binary unions. -/
theorem closed_induction_on_irreducible [IsNoetherian X] (Q : Closeds X → Prop)
    (empty : Q ⊥) (union : ∀ Z W, Q Z → Q W → Q (Z ⊔ W))
    (irreducible : ∀ Z : Closeds X,
      IsIrreducible (Z : Set X) → (∀ W < Z, Q W) → Q Z)
    (Z : Closeds X) : Q Z := by
  apply closed_induction Q _ Z
  intro Z ih
  rcases eq_or_ne Z ⊥ with rfl | hZ
  · exact empty
  by_cases hirr : IsPreirreducible (Z : Set X)
  · exact irreducible Z ⟨Closeds.coe_nonempty.2 hZ, hirr⟩ ih
  simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hirr
  obtain ⟨A, B, hA, hB, hcover, hZA, hZB⟩ := hirr
  lift A to Closeds X using hA
  lift B to Closeds X using hB
  have h := union (Z ⊓ A) (Z ⊓ B)
    (ih _ (inf_lt_left.2 hZA)) (ih _ (inf_lt_left.2 hZB))
  have hcover' : Z ≤ A ⊔ B := hcover
  rwa [← inf_sup_left, inf_eq_left.mpr hcover'] at h

/-- A short exact sequence in which all three terms are coherent in the
locally finitely presented sense used on Noetherian schemes. -/
structure CoherentSequence (S : ShortComplex X.Modules) : Prop where
  shortExact : S.ShortExact
  finite₁ : S.X₁.IsFinitePresentation
  finite₂ : S.X₂.IsFinitePresentation
  finite₃ : S.X₃.IsFinitePresentation

/-- The two-out-of-three hypothesis, restricted to coherent module sheaves. -/
structure TwoOutOfThree (P : X.Modules → Prop) : Prop where
  left : ∀ {S : ShortComplex X.Modules}, CoherentSequence S → P S.X₂ → P S.X₃ → P S.X₁
  middle : ∀ {S : ShortComplex X.Modules}, CoherentSequence S → P S.X₁ → P S.X₃ → P S.X₂
  right : ∀ {S : ShortComplex X.Modules}, CoherentSequence S → P S.X₁ → P S.X₂ → P S.X₃

namespace TwoOutOfThree

variable {P Q : X.Modules → Prop} (hP : TwoOutOfThree P)

include hP

/-- Intersections preserve the coherent two-out-of-three condition. -/
lemma inf (hQ : TwoOutOfThree Q) : TwoOutOfThree (fun M ↦ P M ∧ Q M) where
  left h h₂ h₃ := ⟨hP.left h h₂.1 h₃.1, hQ.left h h₂.2 h₃.2⟩
  middle h h₁ h₃ := ⟨hP.middle h h₁.1 h₃.1, hQ.middle h h₁.2 h₃.2⟩
  right h h₁ h₂ := ⟨hP.right h h₁.1 h₂.1, hQ.right h h₁.2 h₂.2⟩

/-- A comparison by two extensions with the same left term transfers the property
when both error quotients have it. -/
lemma common_subobject {S T : ShortComplex X.Modules}
    (hS : CoherentSequence S) (hT : CoherentSequence T) (hST : S.X₁ = T.X₁)
    (hS₃ : P S.X₃) (hT₃ : P T.X₃) : P S.X₂ ↔ P T.X₂ := by
  constructor
  · intro hS₂
    have hS₁ := hP.left hS hS₂ hS₃
    rw [hST] at hS₁
    exact hP.middle hT hS₁ hT₃
  · intro hT₂
    have hT₁ := hP.left hT hT₂ hT₃
    rw [← hST] at hT₁
    exact hP.middle hS hT₁ hS₃

/-- A comparison by two extensions with the same quotient transfers the property
when both kernels have it. -/
lemma common_quotient {S T : ShortComplex X.Modules}
    (hS : CoherentSequence S) (hT : CoherentSequence T) (hST : S.X₃ = T.X₃)
    (hS₁ : P S.X₁) (hT₁ : P T.X₁) : P S.X₂ ↔ P T.X₂ := by
  constructor
  · intro hS₂
    have hS₃ := hP.right hS hS₁ hS₂
    rw [hST] at hS₃
    exact hP.middle hT hT₁ hS₃
  · intro hT₂
    have hT₃ := hP.right hT hT₁ hT₂
    rw [← hST] at hT₃
    exact hP.middle hS hS₁ hT₃

/-- The extension argument for a finite filtration, expressed by actual coherent
short exact sequences between successive sheaves. -/
lemma finite_extensions (M : ℕ → X.Modules) (G : ℕ → X.Modules) (n : ℕ)
    (f : ∀ i, M i ⟶ M (i + 1)) (g : ∀ i, M (i + 1) ⟶ G i)
    (zero : ∀ i, f i ≫ g i = 0)
    (seq : ∀ i < n, CoherentSequence (ShortComplex.mk (f i) (g i) (zero i)))
    (initial : P (M 0)) (factors : ∀ i < n, P (G i)) : P (M n) := by
  have step : ∀ k, k ≤ n → P (M k) := by
    intro k
    induction k with
    | zero => exact fun _ ↦ initial
    | succ k ih =>
      intro hk
      exact hP.middle (seq k (Nat.lt_of_succ_le hk))
        (ih (Nat.le_of_succ_le hk)) (factors k (Nat.lt_of_succ_le hk))
  exact step n le_rfl

/-- In a coherent filtration, the total sheaf and all but one factor determine
the property for the remaining factor, provided it holds at the initial term. -/
lemma remaining_factor (M : ℕ → X.Modules) (G : ℕ → X.Modules) (n j : ℕ)
    (hj : j < n) (f : ∀ i, M i ⟶ M (i + 1)) (g : ∀ i, M (i + 1) ⟶ G i)
    (zero : ∀ i, f i ≫ g i = 0)
    (seq : ∀ i < n, CoherentSequence (ShortComplex.mk (f i) (g i) (zero i)))
    (initial : P (M 0)) (total : P (M n))
    (factors : ∀ i < n, i ≠ j → P (G i)) : P (G j) := by
  have before : P (M j) := hP.finite_extensions M G j f g zero
    (fun i hi ↦ seq i (hi.trans hj)) initial
    (fun i hi ↦ factors i (hi.trans hj) (Nat.ne_of_lt hi))
  have after : P (M (j + 1)) := by
    apply Nat.decreasingInduction' (P := fun k ↦ P (M k)) _ hj total
    intro k hk hjk next
    exact hP.left (seq k hk) next (factors k hk (Nat.ne_of_gt hjk))
  exact hP.right (seq j hj) before after

end TwoOutOfThree

end FLT.Mazur.FCurve.CoherentDevissage
