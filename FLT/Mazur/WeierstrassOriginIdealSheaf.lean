/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginNeighborhoodCover
public import FLT.Mazur.WeierstrassIntegralSeparated
public import FLT.Mazur.PolygonDivisorPowerPullback

/-!
# The intrinsic origin ideal on the actual parameter neighborhood

The original zero section is closed. Its intrinsic ideal sheaf restricts to
the augmentation kernel already computed in the parameter ring; every power
has the corresponding power of the original regular parameter as equation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

instance integralCurveZero_isClosedImmersion : IsClosedImmersion (integralCurveZero W) :=
  FCurve.isClosedImmersion_section _ _ (integralCurveZero_structure W)

instance originNeighborhoodSection_isClosedImmersion :
    IsClosedImmersion (originNeighborhoodSection W) := by
  have : IsClosedImmersion (originNeighborhoodSection W ≫ originNeighborhoodInclusion W) := by
    rw [originNeighborhoodSection_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp (originNeighborhoodSection W)
    (originNeighborhoodInclusion W)

/-- The intrinsic origin ideal restricts to the original neighborhood section ideal. -/
theorem originIdealSheaf_neighborhood :
    (integralCurveZero W).ker.comap (originNeighborhoodInclusion W) =
      (originNeighborhoodSection W).ker := by
  have : IsClosedImmersion (originNeighborhoodSection W ≫ originNeighborhoodInclusion W) := by
    rw [originNeighborhoodSection_inclusion]
    infer_instance
  rw [← originNeighborhoodSection_inclusion, ProjectiveLineMarkedCharts.ker_comap_mono]

/-- Every intrinsic power restricts to the same power of the original neighborhood ideal. -/
theorem originIdealSheaf_power_neighborhood (n : ℕ) :
    ((integralCurveZero W).ker ^ n).comap (originNeighborhoodInclusion W) =
      (originNeighborhoodSection W).ker ^ n := by
  rw [FCurve.idealSheaf_comap_pow, originIdealSheaf_neighborhood]

/-- The coordinate equation of the actual neighborhood ideal is the original regular parameter. -/
theorem originIdealSheaf_coordinate :
    ((originNeighborhoodSection W).ker.ideal ⟨⊤, isAffineOpen_top _⟩).comap
      (Scheme.ΓSpecIso (.of (OriginNeighborhood W))).inv.hom =
        Ideal.span {originCoordinate W 0} := by
  rw [Scheme.ker_of_isAffine]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id]
  rw [CategoryTheory.Functor.map_id]
  simp only [CommRingCat.hom_id, Ideal.map_id]
  rw [← originEvaluation_kernel]
  ext a
  change (originNeighborhoodSection W).appTop.hom
    ((Scheme.ΓSpecIso (.of (OriginNeighborhood W))).inv.hom a) = 0 ↔
      originEvaluation W a = 0
  have he := congrArg (fun f ↦ f.hom a) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (originEvaluation W).toRingHom))
  change (Scheme.ΓSpecIso (.of R)).inv.hom (originEvaluation W a) =
    (originNeighborhoodSection W).appTop.hom
      ((Scheme.ΓSpecIso (.of (OriginNeighborhood W))).inv.hom a) at he
  rw [← he]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of R)).inv).injective

/-- Each intrinsic origin power has exactly the corresponding regular parameter equation. -/
theorem originIdealSheaf_power_coordinate (n : ℕ) :
    (((originNeighborhoodSection W).ker ^ n).ideal ⟨⊤, isAffineOpen_top _⟩).comap
      (Scheme.ΓSpecIso (.of (OriginNeighborhood W))).inv.hom =
        Ideal.span {originCoordinate W 0 ^ n} := by
  let e := (Scheme.ΓSpecIso (.of (OriginNeighborhood W))).commRingCatIsoToRingEquiv
  let I := (originNeighborhoodSection W).ker.ideal ⟨⊤, isAffineOpen_top _⟩
  have hc : Ideal.map e.toRingHom I = Ideal.span {originCoordinate W 0} :=
    (Ideal.map_comap_of_equiv e).trans (originIdealSheaf_coordinate W)
  change Ideal.comap e.symm.toRingHom (I ^ n) = _
  calc
    _ = Ideal.map e.toRingHom (I ^ n) := (Ideal.map_comap_of_equiv e).symm
    _ = Ideal.map e.toRingHom I ^ n := Ideal.map_pow _ _ _
    _ = Ideal.span {originCoordinate W 0} ^ n := congrArg (fun J ↦ J ^ n) hc
    _ = _ := Ideal.span_singleton_pow _ _

end FLT.Mazur.WeierstrassIntegralChart
