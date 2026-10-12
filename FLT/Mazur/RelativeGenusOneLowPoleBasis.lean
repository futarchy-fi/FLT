/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneCanonicalBasis
public import FLT.Mazur.RelativeGenusOnePointSplit
public import FLT.Mazur.SectionPoleAdaptedBasis

/-!
# Normalized order-two and order-three lifts on the original family

Starting with the actual canonical section, prescribed leading-line frames
construct normalized lifts and bases compatible with the original inclusions.
The positive cohomology vanishing is supplied by the genus-one family itself.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)

/-- The degree-one tensor-power basis comes from the actual canonical divisor section. -/
def relativePointOneBasis : Basis Unit Γ(S, ⊤)
    (ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) 1) 0) :=
  (relativeCanonicalSectionBasis G hg s hI).map
    (((moduleRingHFunctor G.hom.appTop.hom 0).mapIso
      (rightUnitor (divisorLineBundle s.left.ker hI)).symm).toLinearEquiv)

/-- The degree-one tensor unitor recovers the original canonical section. -/
theorem relativePointOneBasis_section :
    (rightUnitor (divisorLineBundle s.left.ker hI)).hom.app ⊤
      (moduleH0Equiv _ (relativePointOneBasis G hg s hI ())) = divisorSection hI ⊤ := by
  rw [relativePointOneBasis, Basis.map_apply]
  change (rightUnitor _).hom.app ⊤
    (moduleH0Equiv _ (moduleHMap (rightUnitor _).inv 0
      (relativeCanonicalSectionBasis G hg s hI ()))) = _
  rw [moduleH0Equiv_naturality]
  have he := ConcreteCategory.congr_hom (congrArg (fun a ↦ a.app ⊤)
    (rightUnitor (divisorLineBundle s.left.ker hI)).inv_hom_id)
  exact (he _).trans (relativeCanonicalSectionBasis_apply G hg s hI)

/-- Every positive pole degree has an actual lift with the prescribed unit leading term. -/
def relativePointNormalizedLift (m : ℕ) (hm : 0 < m)
    (e : Γ(sectionPoleLine s.left hI (m + 1), ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) (m + 1)) 0 := by
  letI := relative_pointPower_acyclic G hg s hI m hm 0
  exact sectionPoleNormalizedLift G.hom s.left s.w hI m e

/-- The constructed lift has leading coefficient exactly one in the actual line frame. -/
theorem relativePointNormalizedLift_leading (m : ℕ) (hm : 0 < m)
    (e : Γ(sectionPoleLine s.left hI (m + 1), ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    e (sectionPoleLeading G.hom s.left s.w hI m
      (relativePointNormalizedLift G hg s hI m hm e)) = 1 := by
  let _ := relative_pointPower_acyclic G hg s hI m hm 0
  exact sectionPoleNormalizedLift_leading G.hom s.left s.w hI m e

/-- The canonical section and a normalized order-two lift form a basis. -/
def relativePointTwoBasis
    (e : Γ(sectionPoleLine s.left hI 2, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    Basis (Unit ⊕ Unit) Γ(S, ⊤)
      (ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) 2) 0) := by
  letI := relative_pointPower_acyclic G hg s hI 1 (by decide) 0
  exact sectionPoleNormalizedBasis G.hom s.left s.w hI 1
    (relativePointOneBasis G hg s hI) e

/-- The order-three basis extends the original order-two basis by a normalized lift. -/
def relativePointThreeBasis
    (e₂ : Γ(sectionPoleLine s.left hI 2, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (e₃ : Γ(sectionPoleLine s.left hI 3, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    Basis ((Unit ⊕ Unit) ⊕ Unit) Γ(S, ⊤)
      (ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) 3) 0) := by
  letI := relative_pointPower_acyclic G hg s hI 2 (by decide) 0
  exact sectionPoleNormalizedBasis G.hom s.left s.w hI 2
    (relativePointTwoBasis G hg s hI e₂) e₃

/-- The new vector at order two is the actual chosen normalized lift. -/
theorem relativePointTwoBasis_new
    (e : Γ(sectionPoleLine s.left hI 2, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    relativePointTwoBasis G hg s hI e (Sum.inr ()) =
      relativePointNormalizedLift G hg s hI 1 (by decide) e := by
  let _ := relative_pointPower_acyclic G hg s hI 1 (by decide) 0
  exact sectionPoleNormalizedBasis_new G.hom s.left s.w hI 1 _ e

/-- Every order-two vector enters order three by the original divisor transition. -/
theorem relativePointThreeBasis_old
    (e₂ : Γ(sectionPoleLine s.left hI 2, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (e₃ : Γ(sectionPoleLine s.left hI 3, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) (i : Unit ⊕ Unit) :
    relativePointThreeBasis G hg s hI e₂ e₃ (Sum.inl i) =
      divisorPowerRingStep G.hom.appTop.hom hI 2 (relativePointTwoBasis G hg s hI e₂ i) := by
  let _ := relative_pointPower_acyclic G hg s hI 2 (by decide) 0
  exact sectionPoleAdaptedBasis_old G.hom s.left s.w hI 2 _ _ i

/-- The new order-three vector is the actual normalized order-three lift. -/
theorem relativePointThreeBasis_new
    (e₂ : Γ(sectionPoleLine s.left hI 2, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (e₃ : Γ(sectionPoleLine s.left hI 3, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    relativePointThreeBasis G hg s hI e₂ e₃ (Sum.inr ()) =
      relativePointNormalizedLift G hg s hI 2 (by decide) e₃ := by
  let _ := relative_pointPower_acyclic G hg s hI 2 (by decide) 0
  exact sectionPoleNormalizedBasis_new G.hom s.left s.w hI 2 _ e₃

end FLT.Mazur.FCurve
