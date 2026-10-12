/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NeutralTwistDirectImage
public import FLT.Mazur.RelativeGenusOneCanonicalLine
public import FLT.Mazur.SectionDivisorLeadingSections

/-!
# Normalization by the original canonical degree-one section

The original divisor section, without its neutral tensor factor, gives a
canonical trivialization of its direct image. On H0 this yields a basis whose
unique vector is exactly that section and whose coefficient is one.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle
  sectionNeutralTwistIso twistedSectionPushforwardEquiv

variable {X S : Scheme} (f : X ⟶ S) (L : X.Modules)

/-- The ordinary adjoint sends the base unit to the original section. -/
theorem sectionDirectImageMap_one (s : Γ(L, ⊤)) :
    (sectionDirectImageMap f L s).app ⊤ (1 : Γ(S, ⊤)) = s := by
  change (globalSectionHom L s).app (f ⁻¹ᵁ ⊤)
    ((modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ ⊤)
      (((pullbackPushforwardAdjunction f).unit.app (structureModule S)).app ⊤ (1 : Γ(S, ⊤)))) = s
  rw [modulePullbackUnitIso_unit, map_one]
  exact globalSectionHom_top L s

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)

include hg in
/-- The original canonical section trivializes the actual divisor-line direct image. -/
theorem relative_canonicalSectionMap_isIso :
    IsIso (sectionDirectImageMap G.hom _ (divisorSection hI ⊤)) := by
  have he := neutralTwist_directImage G.hom (divisorLineBundle s.left.ker hI)
    (divisorSection hI ⊤)
  have hi := relative_canonicalSection_directImage_isIso G hg s hI
  change IsIso (twistedSectionPushforwardEquiv G.hom _
    structureModule_locallyFreeRankOne
    ((sectionNeutralTwistIso G.hom _).inv.app ⊤ (divisorSection hI ⊤))) at hi
  rw [he] at hi
  exact IsIso.of_isIso_comp_left moduleSheafDualUnitIso.hom _

/-- The canonical, untwisted section isomorphism over the original base. -/
def relativeCanonicalSectionIso :
    structureModule S ≅ (pushforward G.hom).obj (divisorLineBundle s.left.ker hI) := by
  let _ := relative_canonicalSectionMap_isIso G hg s hI
  exact asIso (sectionDirectImageMap G.hom _ (divisorSection hI ⊤))

/-- The degree-one coefficient is linear over the original base ring. -/
def relativeCanonicalSectionCoefficient :
    ModuleRingH G.hom.appTop.hom (divisorLineBundle s.left.ker hI) 0 ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤) :=
  (ringHZeroPushforwardSections G.hom _).trans
    (((AffineModuleGlobalSections.sections S).mapIso
      (relativeCanonicalSectionIso G hg s hI).symm).toLinearEquiv)

/-- The inverse coefficient sends one to the original canonical section. -/
theorem relativeCanonicalSectionCoefficient_symm_one :
    ringHZeroPushforwardSections G.hom _
      ((relativeCanonicalSectionCoefficient G hg s hI).symm 1) = divisorSection hI ⊤ := by
  change ringHZeroPushforwardSections G.hom _
    ((ringHZeroPushforwardSections G.hom _).symm
      ((relativeCanonicalSectionIso G hg s hI).hom.app ⊤ (1 : Γ(S, ⊤)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact sectionDirectImageMap_one G.hom _ _

/-- The basis is normalized by the actual canonical section, not an arbitrary line frame. -/
def relativeCanonicalSectionBasis :
    Basis Unit Γ(S, ⊤) (ModuleRingH G.hom.appTop.hom (divisorLineBundle s.left.ker hI) 0) :=
  (Basis.singleton Unit Γ(S, ⊤)).map (relativeCanonicalSectionCoefficient G hg s hI).symm

/-- The unique basis vector is the original divisor section on global sections. -/
theorem relativeCanonicalSectionBasis_apply :
    ringHZeroPushforwardSections G.hom _ (relativeCanonicalSectionBasis G hg s hI ()) =
      divisorSection hI ⊤ := by
  rw [relativeCanonicalSectionBasis, Basis.map_apply, Basis.singleton_apply]
  exact relativeCanonicalSectionCoefficient_symm_one G hg s hI

end FLT.Mazur.FCurve
