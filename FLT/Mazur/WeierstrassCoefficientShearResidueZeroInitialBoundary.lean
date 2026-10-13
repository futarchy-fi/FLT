/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorCoconeMaps
public import FLT.Mazur.WeierstrassCoefficientShearInitialSlopeProjections
public import FLT.Mazur.WeierstrassCoefficientShearInitialAtlasPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorCoconeMaps

/-!
# The full start-zero initial boundary in the actual coefficient atlas

Its initial projection is the full slope isomorphism. Its retained projection
is the punctured original incidence line, with no condition on the conic constant.
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
local notation "x" => WeierstrassDilatation.x W (π ^ 0) (d).b3 (d).b4 (d).b6
local notation "t₀" => WeierstrassModificationX.t W (π ^ 0) (d).b3 (d).b4 (d).b6
local notation "u₀" => coord W (π ^ 0) π (e).b3 (e).b4 (e).b6 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t₀
  (WeierstrassModificationX.overlapEquiv W (π ^ 0) (d).b3 (d).b4 (d).b6)
local notation "B" => PrincipalOpenTensor.transitionIso Q x u₀ (previousBoundaryEquiv hπ d e)
local notation "ci" => incidenceCoefficientShearIso W (π ^ 0) (d).b3 (d).b4 (d).b6 Q r
local notation "cj" => successiveCoefficientShearIso W (π ^ 0) π (e).b3 (e).b4 (e).b6 Q r
local notation "I" => coefficientShearResidueZeroInitialIso hπ hm data s hs
local notation "f" => (A).inv ≫ PrincipalOpenTensor.inclusion Q t₀ ≫ (ci).inv
local notation "g" => (B).inv ≫ PrincipalOpenTensor.inclusion Q u₀ ≫ (cj).inv
local notation "E" => coefficientShearInitialSlopeBoundaryEquiv hπ d e Q r hp h3 h4 hr

/-- The entire original common principal boundary is the complete slope localization. -/
def coefficientShearResidueZeroInitialBoundaryIso :=
  Scheme.Spec.mapIso (E).toRingEquiv.toCommRingCatIso.op
local notation "K" => coefficientShearResidueZeroInitialBoundaryIso hπ hm data s hs h3 h4
local notation "p" => Spec.map (CommRingCat.ofHom
  (algebraMap (Polynomial Q) (SlopeOpen (U).a₁)))
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap
  W (π ^ 0) π (e).b3 (e).b4 (e).b6 Q r hscale hp h3 h4 hr).toRingHom)

/-- The whole original boundary projects to the entire initial equation isomorphically. -/
theorem coefficientShearResidueZeroInitialBoundary_initial : (K).hom ≫ f = (I).hom := by
  apply (cancel_mono (ci).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  have H := coefficientShearInitialSlopeBoundary_initial hπ d e Q r hp h3 h4 hr
    (gc).1 (gc).2.1 (gc).2.2
  have H' := RingHom.ext (AlgHom.congr_fun H)
  exact H'

/-- The other projection is the complete punctured incidence line of the original retained chart. -/
theorem coefficientShearResidueZeroInitialBoundary_retained :
    (K).hom ≫ g = p ≫ L ≫ (cj).inv := by
  apply (cancel_mono (cj).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  have H := coefficientShearInitialSlopeBoundary_retained hπ d e Q r hp h3 h4 hr
    (algebraMap _ _ z)
  have H' := tensorShearScaleOneHorizontalEquiv_base W (π ^ 0) π
    (e).b3 (e).b4 (e).b6 Q r hscale hp h3 h4 hr z
  exact H.trans H'

variable [IsBezout R]
local notation "atlas" => coefficientShearAtlasMap hπ data Q r (s + 1) hs

/-- These whole slope projections form the full actual initial/first-retained pullback. -/
theorem coefficientShearResidueZeroInitialBoundary_isPullback :
    IsPullback (I).hom (p ≫ L ≫ (cj).inv)
      (atlas (.inl 2)) (atlas (.inr ⟨0, Nat.zero_lt_succ s⟩)) := by
  apply (coefficientShearInitialAtlas_isPullback hπ data Q r (s + 1) hs (by omega)).of_iso'
    K (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using
      coefficientShearResidueZeroInitialBoundary_initial hπ hm data s hs h3 h4
  · simpa only [Iso.refl_hom, Category.comp_id] using
      coefficientShearResidueZeroInitialBoundary_retained hπ hm data s hs h3 h4
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
