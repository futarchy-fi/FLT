/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneCanonicalConstants
public import FLT.Mazur.RelativeGenusOneLowPoleBasis

/-!
# The canonical degree-zero to degree-one pole step

The original divisor inclusion sends the normalized constant basis to the
normalized degree-one basis. This is compatibility of the actual map, not
merely an abstract identification of two free rank-one modules.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle

variable {X : Scheme} {R : Type} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- The original ring-linear transition is the original tensorized section map on H0. -/
theorem divisorPowerRingStep_sections (m : ℕ)
    (x : ModuleRingH ρ (tensorPower (divisorLineBundle I hI) m) 0) :
    moduleH0Equiv _ (divisorPowerRingStep ρ hI m x) =
      (divisorTwistedComplex hI (tensorPower (divisorLineBundle I hI) m)).f.app ⊤
        ((leftUnitor (tensorPower (divisorLineBundle I hI) m)).inv.app ⊤
          (moduleH0Equiv _ x)) := by
  change moduleH0Equiv _ (moduleHMap _ 0 (moduleHMap _ 0 x)) = _
  rw [moduleH0Equiv_naturality, moduleH0Equiv_naturality]
  rfl

/-- In degree zero, undoing the left unit comparison takes one to the pure unit tensor. -/
theorem structure_leftUnitor_inv_one :
    (leftUnitor (structureModule X)).inv.app ⊤ (1 : Γ(X, ⊤)) =
      pure (structureModule X) (structureModule X) ⊤ (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤)) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((leftUnitor (structureModule X)).hom.app ⊤)).injective
  have he := congrArg (fun a : structureModule X ⟶ structureModule X ↦
    a.app ⊤ (1 : Γ(X, ⊤))) (leftUnitor (structureModule X)).inv_hom_id
  simp only [Hom.id_app, ConcreteCategory.id_apply] at he
  exact he.trans ((leftUnitor_pure (structureModule X) ⊤
    (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤))).trans (one_smul _ _)).symm

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hJ : EffectiveCartier s.left.ker)

/-- The original pole step sends the canonical constant to the canonical degree-one vector. -/
theorem relativePoint_initial_step :
    divisorPowerRingStep G.hom.appTop.hom hJ 0 (relativePointZeroBasis G hg s hJ ()) =
      relativePointOneBasis G hg s hJ () := by
  apply (moduleH0Equiv _).injective
  apply (ConcreteCategory.bijective_of_isIso
    ((rightUnitor (divisorLineBundle s.left.ker hJ)).hom.app ⊤)).injective
  apply Eq.trans ?_ (relativePointOneBasis_section G hg s hJ).symm
  rw [divisorPowerRingStep_sections]
  have hz := relativePointZeroBasis_section G hg s hJ
  have hu := structure_leftUnitor_inv_one (X := G.left)
  let d := (divisorTwistedComplex hJ (structureModule G.left)).f
  apply Eq.trans (congrArg (fun z : Γ(G.left, ⊤) ↦
    (rightUnitor (divisorLineBundle s.left.ker hJ)).hom.app ⊤
      (d.app ⊤ ((leftUnitor (structureModule G.left)).inv.app ⊤ z))) hz)
  apply Eq.trans (congrArg (fun z ↦
    (rightUnitor (divisorLineBundle s.left.ker hJ)).hom.app ⊤ (d.app ⊤ z)) hu)
  change (rightUnitor _).hom.app ⊤
    ((map (divisorSectionMap hJ) (𝟙 (structureModule G.left))).app ⊤
      (pure _ _ ⊤ (1 : Γ(G.left, ⊤)) (1 : Γ(G.left, ⊤)))) = _
  rw [map_pure]
  exact (rightUnitor_pure _ ⊤ (1 : Γ(G.left, ⊤)) (divisorSection hJ ⊤)).trans
    (one_smul _ _)

end FLT.Mazur.FCurve
