/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineInfinityTorusTransition
public import FLT.Mazur.SchemeOpenPushoutCoverIso

/-!
# The projective line as the exact original slope/Laurent gluing

The intersection with the left chart is the whole Laurent open T-1.
The given two-root slope chart is therefore the full cartesian intersection,
and its canonical pushout is the projective line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLine
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a : Kˣ)
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial (a : K))
local notation "m" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (slopeLaurentMap a)))

/-- The exact inverse image of the left line is the entire torus punctured at one. -/
theorem infinityTorus_preimage_left : (infinityTorusChart a) ⁻¹' Set.range (left K) =
    (PrimeSpectrum.basicOpen (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹]) :
      Set (PrimeSpectrum K[T;T⁻¹])) := by
  change (infinityTorusToRight a) ⁻¹' ((right K) ⁻¹' Set.range (left K)) = _
  rw [right_preimage_left_basicOpen]
  ext x
  change infinityTorusMap a X ∉ x.asIdeal ↔ LaurentPolynomial.T 1 - 1 ∉ x.asIdeal
  rw [infinityTorusMap_X]
  exact not_congr (x.asIdeal.unit_mul_mem_iff_mem
    ((a⁻¹).isUnit.map (LaurentPolynomial.C : K →+* K[T;T⁻¹])))

/-- The entire original two-root slope open is the full intersection of the new cover. -/
theorem infinityTorus_isPullback : IsPullback s m (left K) (infinityTorusChart a) := by
  apply IsOpenImmersion.isPullback s m (left K) (infinityTorusChart a)
    (infinityTorus_slope_condition a).symm
  apply TopologicalSpace.Opens.ext
  change (infinityTorusChart a) ⁻¹' Set.range (left K) = Set.range m
  rw [infinityTorus_preimage_left, slopeLaurentMap_range]

/-- The full original slope/Laurent gluing is the projective line. -/
def infinityTorusGluingIso : pushout s m ≅ scheme K :=
  SchemeOpenPushout.coverIso s m (left K) (infinityTorusChart a)
    (infinityTorus_isPullback a) (infinityTorus_charts_cover a)

/-- The comparison fixes every point and function of the original slope affine line. -/
@[reassoc] theorem infinityTorusGluingIso_left :
    pushout.inl s m ≫ (infinityTorusGluingIso a).hom = left K :=
  SchemeOpenPushout.inl_coverIso _ _ _ _ _ _

/-- The entire original Laurent infinity chart retains its translated coordinate. -/
@[reassoc] theorem infinityTorusGluingIso_right :
    pushout.inr s m ≫ (infinityTorusGluingIso a).hom = infinityTorusChart a :=
  SchemeOpenPushout.inr_coverIso _ _ _ _ _ _

/-- The fixed projective line realizes the canonical slope/Laurent pushout square. -/
theorem infinityTorus_isPushout : IsPushout s m (left K) (infinityTorusChart a) := by
  apply (IsPushout.of_hasPushout s m).of_iso'
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (infinityTorusGluingIso a).symm
  · simp
  · simp
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
    rw [← infinityTorusGluingIso_left a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
    rw [← infinityTorusGluingIso_right a, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.ProjectiveLine
