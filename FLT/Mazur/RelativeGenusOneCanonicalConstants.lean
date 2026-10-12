/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneCanonicalBasis

/-!
# Canonical degree-zero sections of the original family

Generation by the canonical degree-one section and injectivity of its Cartier
map show that every global function is pulled from the base, uniquely. The
resulting degree-zero basis has the original constant section one as its vector.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle

variable {X S : Scheme} (f : X ⟶ S) (L : X.Modules)

/-- The ordinary direct-image section map retains the original base scalar action. -/
theorem sectionDirectImageMap_scalar (s : Γ(L, ⊤)) (r : Γ(S, ⊤)) :
    (show Γ(L, ⊤) from (sectionDirectImageMap f L s).app ⊤ r) = f.appTop r • s := by
  have h := (sectionDirectImageMap f L s).app_smul r (1 : Γ(S, ⊤))
  rw [sectionDirectImageMap_one] at h
  exact (congrArg ((sectionDirectImageMap f L s).app ⊤) (mul_one r)).symm.trans h

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)

include hg s hI in
/-- The original structure-ring map is bijective, derived from canonical-section generation. -/
theorem relative_point_structureMap_bijective : Function.Bijective G.hom.appTop.hom := by
  let _ := relative_canonicalSectionMap_isIso G hg s hI
  let a := sectionDirectImageMap G.hom _ (divisorSection hI ⊤)
  have ha := ConcreteCategory.bijective_of_isIso (a.app ⊤)
  constructor
  · intro r t h
    apply ha.injective
    change (sectionDirectImageMap G.hom _ _).app ⊤ r =
      (sectionDirectImageMap G.hom _ _).app ⊤ t
    exact (sectionDirectImageMap_scalar G.hom _ _ r).trans
      ((congrArg (fun z : Γ(G.left, ⊤) ↦ z • divisorSection hI ⊤) h).trans
        (sectionDirectImageMap_scalar G.hom _ _ t).symm)
  · intro z
    obtain ⟨r, hr⟩ := ha.surjective ((divisorSectionMap hI).app ⊤ z)
    refine ⟨r, divisorSectionMap_injective hI ⊤ ?_⟩
    rw [divisorSectionMap_app]
    exact (sectionDirectImageMap_scalar G.hom _ _ r).symm.trans hr

/-- The canonical global-function comparison uses exactly the original structure-ring map. -/
def relativePointConstantsRingEquiv : Γ(S, ⊤) ≃+* Γ(G.left, ⊤) :=
  RingEquiv.ofBijective G.hom.appTop.hom (relative_point_structureMap_bijective G hg s hI)

/-- On sections with the original base action, scalar multiples of one give an equivalence. -/
def relativePointConstantsSections :
    Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] Γ((pushforward G.hom).obj (structureModule G.left), ⊤) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(S, ⊤)
    Γ((pushforward G.hom).obj (structureModule G.left), ⊤) (1 : Γ(G.left, ⊤))) (by
    change Function.Bijective (fun r : Γ(S, ⊤) ↦ G.hom.appTop r * 1)
    simpa only [mul_one] using relative_point_structureMap_bijective G hg s hI)

/-- The degree-zero cohomology basis is canonically normalized by the constant section one. -/
def relativePointZeroBasis :
    Basis Unit Γ(S, ⊤) (ModuleRingH G.hom.appTop.hom (structureModule G.left) 0) :=
  (Basis.singleton Unit Γ(S, ⊤)).map
    ((relativePointConstantsSections G hg s hI).trans
      (ringHZeroPushforwardSections G.hom (structureModule G.left)).symm)

/-- The constructed degree-zero vector is the original constant function one. -/
theorem relativePointZeroBasis_section :
    moduleH0Equiv _ (relativePointZeroBasis G hg s hI ()) = (1 : Γ(G.left, ⊤)) := by
  rw [relativePointZeroBasis, Basis.map_apply, Basis.singleton_apply]
  change ringHZeroPushforwardSections G.hom _
    ((ringHZeroPushforwardSections G.hom _).symm
      (relativePointConstantsSections G hg s hI 1)) = _
  rw [LinearEquiv.apply_symm_apply]
  change G.hom.appTop 1 * 1 = 1
  rw [map_one, mul_one]

end FLT.Mazur.FCurve
