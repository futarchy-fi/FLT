/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticIntegralSectionReduction
public import FLT.Mazur.WeierstrassSmoothCoefficientPreimage
public import FLT.Mazur.WeierstrassSmoothConnected

/-!
# The original section in the actual special-fiber cubic

The Cartesian coefficient comparison transports the closed restriction of the
integral section to the residue-field cubic. Smooth reduction is exactly
membership in the image of the connected component of its smooth zero point.
This identifies the Weierstrass smooth component, before comparison with a
separate generalized elliptic model.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Specialization still lies over the actual residue map. -/
@[reassoc] theorem integralPointSpecialization_structure
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    integralPointSpecialization A W P ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (residue A)) := by
  rw [integralPointSpecialization, Category.assoc, integralPointSection_structure,
    Category.comp_id]

/-- The original point's specialization as a point of the actual residue-field cubic. -/
def integralPointClosedFiber (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec (.of (ResidueField A)) ⟶ integralCurve (W.map (residue A)) :=
  pullback.lift (integralPointSpecialization A W P) (𝟙 _)
    (by rw [Category.id_comp]; exact integralPointSpecialization_structure A W P) ≫
      (integralCurveCoefficientBaseChangeIso W).inv

/-- Inclusion of the closed-fiber point recovers the original specialized section. -/
@[reassoc] theorem integralPointClosedFiber_coefficient
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    integralPointClosedFiber A W P ≫ integralCoefficientMorphism W =
      integralPointSpecialization A W P := by
  rw [integralPointClosedFiber, Category.assoc,
    ← integralCurveCoefficientBaseChangeIso_fst, Iso.inv_hom_id_assoc, pullback.lift_fst]

/-- The point of the special-fiber cubic is a section over the residue field. -/
@[reassoc] theorem integralPointClosedFiber_structure
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    integralPointClosedFiber A W P ≫ integralCurveStructure (W.map (residue A)) = 𝟙 _ := by
  change integralPointClosedFiber A W P ≫
    integralCurveStructure (W.map (algebraMap A (ResidueField A))) = _
  rw [integralPointClosedFiber, Category.assoc,
    ← integralCurveCoefficientBaseChangeIso_snd (S := ResidueField A) W,
    Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- Arithmetic E₀ is smoothness in the actual special-fiber cubic. -/
theorem integralPointClosedFiber_smooth_iff
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Set.range (integralPointClosedFiber A W P) ⊆ integralSmoothOpen (W.map (residue A)) ↔
      SmoothReduction A W P := by
  rw [← integralPointSpecialization_smooth_iff,
    ← integralPointClosedFiber_coefficient A W P]
  constructor
  · intro h
    rintro _ ⟨z, rfl⟩
    have hz := h ⟨z, rfl⟩
    exact (integralCoefficientMorphism_preimage_smooth W).ge hz
  · intro h z hz
    obtain ⟨x, rfl⟩ := hz
    exact (integralCoefficientMorphism_preimage_smooth W).le (h ⟨x, rfl⟩)

/-- E₀ is exactly the inverse image of the genuine zero connected component of the smooth fiber. -/
theorem integralPointClosedFiber_zero_component_iff
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Set.range (integralPointClosedFiber A W P) ⊆
        (integralSmoothOpen (W.map (residue A))).ι ''
          connectedComponent (integralSmoothZero (W.map (residue A))
            (closedPoint (ResidueField A))) ↔ SmoothReduction A W P := by
  rw [integralSmoothZero_component_image]
  exact integralPointClosedFiber_smooth_iff A W P

end FLT.Mazur.WeierstrassIntegralChart
