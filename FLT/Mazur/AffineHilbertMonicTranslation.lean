/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertInvariantPrincipalEffectiveness

/-!
# Nonvanishing invariant denominators for monic translations

A translation whose structural morphism is monic has no independent second
sheet. Reflexivity then proves that each original open chart fills its
entire tensor envelope. In particular the constructed invariant denominator
ideal contains one, which does not vanish at any source point.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
  [Mono V.hom]
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "e" => equivalence f hL d V c k

omit [Algebra.FiniteType ℤ R] in
/-- The original envelope projection is monic when translation has only one sheet. -/
theorem monicTranslation_envelopeProjection_mono : Mono π := by
  have H := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)
  exact H.mono_fst_of_mono

/-- Reflexivity constructs an actual inverse to the original full envelope inclusion. -/
theorem monicTranslation_toEnvelope_isIso : IsIso j := by
  let _ := monicTranslation_envelopeProjection_mono (A := A) V
  have hjπ : j ≫ π = (snd f hL d V c k).left :=
    congrArg Over.Hom.left (toEnvelope_test f hL d V c k)
  have hr : (e).r.left ≫ j ≫ π = 𝟙 A.left := by
    rw [hjπ]
    exact congrArg Over.Hom.left (e).reflexivity₂
  have h : (π ≫ (e).r.left) ≫ j = 𝟙 _ := by
    apply (cancel_mono π).mp
    simp only [Category.assoc, hr, Category.comp_id, Category.id_comp]
  exact ⟨⟨π ≫ (e).r.left, (cancel_mono j).mp (by
    rw [Category.assoc, h, Category.comp_id, Category.id_comp]), h⟩⟩

/-- The admissible ideal is constructed to be the unit ideal in this case. -/
theorem monicTranslation_denominators_eq_top :
    invariantEnvelopeDenominators f hL d V c k = ⊤ :=
  (invariantEnvelopeDenominators_eq_top_iff f hL d V c k).mpr
    (monicTranslation_toEnvelope_isIso f hL d V c k)

/-- A concrete admissible coefficient is nonvanishing at every original source point. -/
theorem monicTranslation_nonvanishing (x : A.left) :
    ∃ r : SchemeEffectiveEpiSections.compatibleFunctions (fst f hL d V c k).left
        (snd f hL d V c k).left,
      r ∈ invariantEnvelopeDenominators f hL d V c k ∧ x ∈ A.left.basicOpen r.val := by
  refine ⟨1, ?_, ?_⟩
  · rw [monicTranslation_denominators_eq_top f hL d V c k]
    trivial
  · change x ∈ A.left.basicOpen 1
    simp only [Scheme.basicOpen_one, TopologicalSpace.Opens.mem_top]

end FLT.Mazur.HilbertChart.AffineRestriction
