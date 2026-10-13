/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroInitialBoundary
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorAffine
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroInitialBoundary
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneIncidence
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorCoconeMaps

/-!
# The complete original start-zero slope chart and its contraction

The full initial slope chart is the punctured first retained incidence line.
Its original finite and cubic projections are the original exterior normalization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
set_option maxRecDepth 2048
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨1, by omega⟩
variable (h3 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨1, by omega⟩).b3 = 0)
  (h4 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨1, by omega⟩).b4 = 0)
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ 0) = 1 from by simp
local notation "gc" => coefficientShearResidueZeroInitial_coefficients hπ hm data s hs
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
variable [IsBezout R]
local notation "I" => coefficientShearResidueZeroInitialIso hπ hm data s hs
local notation "q" => Spec.map (CommRingCat.ofHom
  (algebraMap (Polynomial Q) (SlopeOpen (U).a₁)))
local notation "c" => coefficientShearGluedChart hπ data Q r (s + 1) hs
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap
  W (π ^ (0 + 0)) π (e).b3 (e).b4 (e).b6 Q r (by simp) hp h3 h4 hr).toRingHom)
local notation "E" => coefficientShearRetainedScaleOneTensorIso
  data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
local notation "proj" => coefficientShearGluedProjection hπ data Q r (s + 1) hs
local notation "N" => originalResidueFiniteNormalization hπ data (s + 1) hs
  e (by simp) (nodalDepth_residue_uniformizer hm)

/-- The entire initial slope chart is the punctured original retained incidence line. -/
theorem coefficientShearResidueZeroInitialIso_glued :
    (I).hom ≫ c (.inl 2) = q ≫ L ≫ (E).inv ≫ c (.inr ⟨0, Nat.zero_lt_succ s⟩) := by
  apply (cancel_mono (coefficientShearGluedIso hπ data Q r (s + 1) hs).hom).mp
  simp only [Category.assoc, coefficientShearGluedIso_chart]
  have H := (coefficientShearResidueZeroInitialBoundary_isPullback
    hπ hm data s hs h3 h4).w
  simp only [Category.assoc] at H
  exact H

include h3 h4 in
/-- The entire initial chart projects to the actual proper exterior in the finite model. -/
theorem coefficientShearResidueZeroInitialIso_finiteProjection :
    (I).hom ≫ c (.inl 2) ≫ proj = q ≫ ProjectiveLine.left Q ≫ N := by
  rw [← Category.assoc, coefficientShearResidueZeroInitialIso_glued hπ hm data s hs h3 h4]
  simp only [Category.assoc]
  have H (t : ℕ) (ht : t ≤ n) (ht0 : 0 < t) (heq : t = 0 + 1 + s) :
      L ≫ coefficientShearRetainedTensorChart hπ data Q r t ht ⟨0, ht0⟩ ≫
        coefficientShearGluedProjection hπ data Q r t ht =
      ProjectiveLine.left Q ≫ originalResidueFiniteNormalization hπ data t ht
        e (by simp) (nodalDepth_residue_uniformizer hm) := by
    subst t
    have H₀ := coefficientShearResidueZeroIncidence_finiteProjection
      hπ data (by omega) s ht (nodalDepth_residue_uniformizer hm) h3 h4
    simpa only [coefficientShearRetainedScaleOneIncidence, Category.assoc] using H₀
  have H' := H (s + 1) hs (Nat.zero_lt_succ s) (by omega)
  change L ≫ (E).inv ≫ c (.inr ⟨0, Nat.zero_lt_succ s⟩) ≫ proj =
    ProjectiveLine.left Q ≫ N at H'
  exact congrArg (q ≫ ·) H'

include h3 h4 in
/-- Its full original integral cubic projection is the punctured complete normalization. -/
theorem coefficientShearResidueZeroInitialIso_toCurve :
    (I).hom ≫ c (.inl 2) ≫ proj ≫ finiteGlobalContraction hπ data (s + 1) hs =
      q ≫ ProjectiveLine.left Q ≫ originalResidueCompleteNormalization
        e (by simp) (nodalDepth_residue_uniformizer hm) := by
  have H := congrArg (· ≫ finiteGlobalContraction hπ data (s + 1) hs)
    (coefficientShearResidueZeroInitialIso_finiteProjection hπ hm data s hs h3 h4)
  simpa only [Category.assoc, originalResidueFiniteNormalization_contraction] using H

end FLT.Mazur.WeierstrassDividedDepth
