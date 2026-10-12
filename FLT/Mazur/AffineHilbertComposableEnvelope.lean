/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationNeighborhoods

/-!
# An affine envelope for actual composable Picard relation arrows

The composable-pair scheme embeds openly into (A × V) × V. Both independent
translation coordinates survive; the construction uses the full relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => toEnvelope f hL d V c k

/-- The original scheme of composable arrows, before any chart restriction. -/
abbrev composable : Over (Spec (.of R)) := pullback q p

/-- Keep the second arrow and the independent translation coordinate of the first. -/
def composableToProduct : composable f hL d V c k ⟶ prod Z V :=
  prod.lift (pullback.snd q p) (pullback.fst q p ≫ j ≫ prod.snd)

/-- This product square is a base change of the original full relation embedding. -/
theorem composableToProduct_isPullback :
    IsPullback (pullback.fst q p) (composableToProduct f hL d V c k)
      j (prod.map p (𝟙 V)) := by
  apply IsPullback.of_bot (v₂₁ := prod.fst) (v₂₂ := prod.fst) (h₃₁ := p)
  · simpa only [composableToProduct, prod.lift_fst, toEnvelope_test] using
      IsPullback.of_hasPullback q p
  · apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, composableToProduct,
        prod.lift_fst_assoc, toEnvelope_test, pullback.condition]
    · simp only [Category.assoc, prod.map_snd, composableToProduct,
        prod.lift_snd, Category.comp_id]
  · exact (IsPullback.of_prod_fst_with_id p V).flip

variable [IsOpenImmersion k.left]

instance composableToProduct_isOpenImmersion :
    IsOpenImmersion (composableToProduct f hL d V c k).left :=
  MorphismProperty.of_isPullback
    ((composableToProduct_isPullback f hL d V c k).map (Over.forget _))
    (inferInstanceAs (IsOpenImmersion (j).left))

/-- Embed the actual composable arrows into the original three-coordinate affine envelope. -/
def composableToEnvelope : composable f hL d V c k ⟶ prod (prod A V) V :=
  composableToProduct f hL d V c k ≫ prod.map j (𝟙 V)

instance composableToEnvelope_isOpenImmersion :
    IsOpenImmersion (composableToEnvelope f hL d V c k).left := by
  let _ : IsOpenImmersion (prod.map j (𝟙 V)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_prod_fst_with_id j V).map (Over.forget _))
      (inferInstanceAs (IsOpenImmersion (j).left))
  change IsOpenImmersion ((composableToProduct f hL d V c k).left ≫
    (prod.map j (𝟙 V)).left)
  infer_instance

omit [IsOpenImmersion k.left] in
/-- The envelope records the complete second arrow. -/
@[reassoc]
theorem composableToEnvelope_fst :
    composableToEnvelope f hL d V c k ≫ prod.fst = pullback.snd q p ≫ j := by
  simp only [composableToEnvelope, Category.assoc, prod.map_fst,
    composableToProduct, prod.lift_fst_assoc]

omit [IsOpenImmersion k.left] in
/-- The third coordinate is the first arrow's original translation coordinate. -/
@[reassoc]
theorem composableToEnvelope_snd :
    composableToEnvelope f hL d V c k ≫ prod.snd = pullback.fst q p ≫ j ≫ prod.snd := by
  simp only [composableToEnvelope, Category.assoc, prod.map_snd,
    Category.comp_id, composableToProduct, prod.lift_snd]

variable [IsAffine A.left] [IsAffine V.left]

/-- Every finite diagram of composable original arrows has one affine neighborhood. -/
theorem exists_composable_affine_neighborhood
    (W : (composable f hL d V c k).left.Opens)
    (s : Set (composable f hL d V c k).left) (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ U : (composable f hL d V c k).left.Opens,
      IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W := by
  let _ := variableHilbertOverlap_envelope_affine V A
  let _ := variableHilbertOverlap_envelope_affine V (prod A V)
  exact AffineEnvelopeFiniteNeighborhood.exists_affineOpen
    (composableToEnvelope f hL d V c k).left W s hs hsW

end FLT.Mazur.HilbertChart.AffineRestriction
