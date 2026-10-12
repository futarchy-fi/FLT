/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneHigherMonomials
public import FLT.Mazur.SectionPoleSpecifiedBasis

/-!
# Reduction of every original section by a unit-leading monomial

Exactness of the original pole sequence removes the actual leading coefficient
using the constructed higher monomial. The remainder has the preceding pole bound.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  relativePoleFunction

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

/-- The common-frame leading coordinate of the new monomial is exactly one. -/
theorem relativePointHigherMonomial_leading (m : ℕ) :
    sectionPoleLeadingCoordinate G.hom s.left s.w hI (m + 1)
      (sectionPoleMultiplicativeCoordinates s.left hI e (m + 2))
      (relativePointHigherMonomial G hg s hI e m) = 1 :=
  (sectionPoleCoefficient_leading s.left hI e G.hom s.w (m + 1) _).symm.trans
    (relativePointHigherMonomial_coefficient G hg s hI e m)

/-- Subtracting the actual leading monomial leaves an original lower-pole section. -/
theorem relativePointHigherMonomial_decomposition (m : ℕ)
    (z : ModuleRingH G.hom.appTop.hom
      (tensorPower (divisorLineBundle s.left.ker hI) (m + 2)) 0) :
    ∃ w : ModuleRingH G.hom.appTop.hom
        (tensorPower (divisorLineBundle s.left.ker hI) (m + 1)) 0,
      ∃ a : Γ(S, ⊤), z = divisorPowerRingStep G.hom.appTop.hom hI (m + 1) w +
        a • relativePointHigherMonomial G hg s hI e m := by
  let g := sectionPoleLeadingCoordinate G.hom s.left s.w hI (m + 1)
    (sectionPoleMultiplicativeCoordinates s.left hI e (m + 2))
  let v := relativePointHigherMonomial G hg s hI e m
  have hv : g v = 1 := relativePointHigherMonomial_leading G hg s hI e m
  have hz : g (z - g z • v) = 0 := by
    rw [map_sub, g.map_smul, hv, smul_eq_mul, mul_one, sub_self]
  obtain ⟨w, hw⟩ := (sectionPoleLeadingCoordinate_exact G.hom s.left s.w hI (m + 1)
    (sectionPoleMultiplicativeCoordinates s.left hI e (m + 2)) (z - g z • v)).mp hz
  exact ⟨w, g z, (congrArg (fun t ↦ t + g z • v) hw).trans
    (sub_add_cancel z (g z • v)) |>.symm⟩

end FLT.Mazur.FCurve
