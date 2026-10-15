/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryThickeningKernelPair

/-!
# The original infinitesimal boundary tower

Transition maps preserve the whole Hilbert source and every original relation
arrow. Their endpoint squares and cocycle laws hold as scheme morphisms, so
later descent can retain the transverse infinitesimal data at every order.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "I" => boundaryIdealSheaf π O
local notation "B" n:max => originalThickenedSource f hL d V c k n
local notation "i" n:max => originalThickenedSourceMap f hL d V c k n
local notation "C" n:max => originalThickenedRelation f hL d V c k n
local notation "r" n:max => originalThickenedFst f hL d V c k n
local notation "s" n:max => originalThickenedSnd f hL d V c k n
local notation "z" n:max => originalThickenedArrow f hL d V c k n

/-- The actual closed transition between positive infinitesimal orders. -/
def originalThickenedTransition {m n : ℕ} (h : m ≤ n) : B m ⟶ B n :=
  Over.homMk (AffineIdealPower.transition I (Nat.add_le_add_right h 1)) (by
    change _ ≫ (I ^ (n + 1)).subschemeι ≫ A.hom = _
    rw [← Category.assoc, AffineIdealPower.transition_ι]
    rfl)

omit [Etale V.hom] [IsAffine A.left] in
/-- Every infinitesimal transition retains the whole original source map. -/
@[reassoc]
theorem originalThickenedTransition_source {m n : ℕ} (h : m ≤ n) :
    originalThickenedTransition f hL d V c k h ≫ i n = i m := by
  apply Over.OverMorphism.ext
  exact AffineIdealPower.transition_ι I (Nat.add_le_add_right h 1)

attribute [local irreducible] originalThickenedSource originalThickenedSourceMap
  originalThickenedRelation originalThickenedFst originalThickenedSnd originalThickenedArrow

omit [Etale V.hom] [IsAffine A.left] in
/-- The original Hilbert parameter is unchanged by thickening transitions. -/
@[reassoc]
theorem originalThickenedTransition_parameter {m n : ℕ} (h : m ≤ n) :
    originalThickenedTransition f hL d V c k h ≫ (i n ≫ k) = i m ≫ k := by
  rw [originalThickenedTransition_source_assoc]

omit [Etale V.hom] [IsAffine A.left] in
/-- Transitions preserve the original Picard class, including nonreduced tests. -/
theorem originalThickenedTransition_section {m n : ℕ} (h : m ≤ n) :
    (relativeFppfSheaf f).obj.map (originalThickenedTransition f hL d V c k h).op
      (originalThickenedSection f hL d V c k n) =
      originalThickenedSection f hL d V c k m := by
  simp only [originalThickenedSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, originalThickenedTransition_source]

omit [Etale V.hom] [IsAffine A.left] in
/-- Source transitions satisfy the scheme cocycle law. -/
@[reassoc]
theorem originalThickenedTransition_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    originalThickenedTransition f hL d V c k h₁ ≫
      originalThickenedTransition f hL d V c k h₂ =
      originalThickenedTransition f hL d V c k (h₁.trans h₂) := by
  apply (cancel_mono (i n)).mp
  rw [Category.assoc, originalThickenedTransition_source,
    originalThickenedTransition_source, originalThickenedTransition_source]

omit [Etale V.hom] [IsAffine A.left] in
/-- Transitions at equal orders are identities on the whole source. -/
theorem originalThickenedTransition_refl (n : ℕ) :
    originalThickenedTransition f hL d V c k (le_refl n) = 𝟙 _ := by
  apply (cancel_mono (i n)).mp
  rw [originalThickenedTransition_source, Category.id_comp]

/-- The full relation transition retains the original independent arrow. -/
def originalThickenedRelationTransition {m n : ℕ} (h : m ≤ n) : C m ⟶ C n :=
  originalThickenedLift f hL d V c k n (z m)
    (r m ≫ originalThickenedTransition f hL d V c k h) (by
      rw [Category.assoc, originalThickenedTransition_source, originalThickenedArrow_fst])

omit [Etale V.hom] [IsAffine A.left] in
/-- No original relation arrow is changed by passing to a higher order. -/
@[reassoc]
theorem originalThickenedRelationTransition_arrow {m n : ℕ} (h : m ≤ n) :
    originalThickenedRelationTransition f hL d V c k h ≫ z n = z m :=
  originalThickenedLift_arrow f hL d V c k n _ _ _

omit [Etale V.hom] [IsAffine A.left] in
/-- Relation transitions retain the first whole infinitesimal endpoint. -/
@[reassoc]
theorem originalThickenedRelationTransition_fst {m n : ℕ} (h : m ≤ n) :
    originalThickenedRelationTransition f hL d V c k h ≫ r n =
      r m ≫ originalThickenedTransition f hL d V c k h :=
  originalThickenedLift_fst f hL d V c k n _ _ _

/-- Relation transitions retain the independent second infinitesimal endpoint. -/
@[reassoc]
theorem originalThickenedRelationTransition_snd {m n : ℕ} (h : m ≤ n) :
    originalThickenedRelationTransition f hL d V c k h ≫ s n =
      s m ≫ originalThickenedTransition f hL d V c k h := by
  apply (cancel_mono (i n)).mp
  rw [Category.assoc, ← originalThickenedArrow_snd, ← Category.assoc,
    originalThickenedRelationTransition_arrow, Category.assoc,
    originalThickenedTransition_source, originalThickenedArrow_snd]

omit [Etale V.hom] [IsAffine A.left] in
/-- Full relation transitions satisfy their scheme cocycle law. -/
@[reassoc]
theorem originalThickenedRelationTransition_comp {l m n : ℕ}
    (h₁ : l ≤ m) (h₂ : m ≤ n) :
    originalThickenedRelationTransition f hL d V c k h₁ ≫
      originalThickenedRelationTransition f hL d V c k h₂ =
      originalThickenedRelationTransition f hL d V c k (h₁.trans h₂) := by
  apply (cancel_mono (z n)).mp
  rw [Category.assoc, originalThickenedRelationTransition_arrow,
    originalThickenedRelationTransition_arrow, originalThickenedRelationTransition_arrow]

omit [Etale V.hom] [IsAffine A.left] in
/-- Equal-order relation transitions are identities on the full relation scheme. -/
theorem originalThickenedRelationTransition_refl (n : ℕ) :
    originalThickenedRelationTransition f hL d V c k (le_refl n) = 𝟙 _ := by
  apply (cancel_mono (z n)).mp
  rw [originalThickenedRelationTransition_arrow, Category.id_comp]

end FLT.Mazur.HilbertChart.AffineRestriction
