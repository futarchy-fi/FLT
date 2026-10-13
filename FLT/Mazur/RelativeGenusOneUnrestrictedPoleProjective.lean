/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneUnrestrictedLowPoleBasis
public import FLT.Mazur.FlatCoefficientAllCohomology

/-!
# Finite projective original pole sections on arbitrary affine bases

The canonical degree-one basis starts an induction through the actual split
pole steps. Each successive quotient is an invertible base module, so every
positive pole module is finite projective without a Noetherian hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.FCurve.UnrestrictedPole
open ModuleLineBundleTensorPullback IncreasingCechCoefficients Chow
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsAffine S]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)

include hg in
/-- All positive actual pole cohomology modules are finite projective over the original ring. -/
theorem relativePointPole_finite_projective (m : ℕ) (hm : 0 < m) :
    Module.Finite Γ(S, ⊤)
        (ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) m) 0) ∧
      Module.Projective Γ(S, ⊤)
        (ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) m) 0) := by
  induction m, hm using Nat.le_induction with
  | base =>
    exact ⟨Module.Finite.of_basis (relativePointOneBasis G hg s hI),
      Module.Projective.of_basis (relativePointOneBasis G hg s hI)⟩
  | succ m hm ih =>
    let _ := ih.1
    let _ := ih.2
    let _ := sectionPoleLine_sections_invertible (S := S) s.left hI (m + 1)
    let e := (relativePointPoleSplit G hg s hI m hm).val
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

include hg in
/-- The actual base-linear section modules inherit finite projectivity from the pole splitting. -/
theorem relativePointPower_sections_finite_projective (m : ℕ) (hm : 0 < m) :
    Module.Finite Γ(S, ⊤)
        (baseSections (tensorPower (divisorLineBundle s.left.ker hI) m) G.hom.appTop.hom ⊤) ∧
      Module.Projective Γ(S, ⊤)
        (baseSections (tensorPower (divisorLineBundle s.left.ker hI) m) G.hom.appTop.hom ⊤) := by
  obtain ⟨hf, hp⟩ := relativePointPole_finite_projective G hg s hI m hm
  let _ := hf
  let _ := hp
  let e := ringHZeroBaseSections (tensorPower (divisorLineBundle s.left.ker hI) m)
    G.hom.appTop.hom
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

end FLT.Mazur.FCurve.UnrestrictedPole
