/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePoleReduction
public import FLT.Mazur.RelativePoleComplementLinear

/-!
# Compatible monomial bases in every positive relative pole degree

The actual unit-leading products extend the original constant vector at every
step. The finite indices retain their order, and old vectors use original inclusions.
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

/-- Append one last index without changing any preceding finite index. -/
def relativePoleIndexSucc (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

/-- Old indices retain their position in the extended basis. -/
theorem relativePoleIndexSucc_old (n : ℕ) (i : Fin n) :
    (relativePoleIndexSucc n).symm i.castSucc = Sum.inl i := by
  simp only [relativePoleIndexSucc, Equiv.symm_trans_apply,
    finSumFinEquiv_symm_apply_castSucc, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Sum.map_inl, Equiv.refl_symm, Equiv.refl_apply]

/-- The new vector occupies the last position. -/
theorem relativePoleIndexSucc_last (n : ℕ) :
    (relativePoleIndexSucc n).symm (Fin.last n) = Sum.inr () := by
  simp only [relativePoleIndexSucc, Equiv.symm_trans_apply, finSumFinEquiv_symm_last,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr]

/-- A basis in every original positive pole degree, built from actual monomial sections. -/
def relativePointAllPoleBasis : (m : ℕ) → Module.Basis (Fin (m + 1)) Γ(S, ⊤)
    (ModuleRingH G.hom.appTop.hom
      (tensorPower (divisorLineBundle s.left.ker hI) (m + 1)) 0)
  | 0 => (relativePointOneBasis G hg s hI).reindex (Equiv.ofUnique Unit (Fin 1))
  | m + 1 => (sectionPoleSpecifiedBasis G.hom s.left s.w hI (m + 1)
      (sectionPoleMultiplicativeCoordinates s.left hI e (m + 2))
      (relativePointAllPoleBasis m) (relativePointHigherMonomial G hg s hI e m)
      (relativePointHigherMonomial_leading G hg s hI e m)).reindex
        (relativePoleIndexSucc (m + 1))

/-- The first basis retains the original canonical degree-one vector. -/
theorem relativePointAllPoleBasis_zero (i : Fin 1) :
    relativePointAllPoleBasis G hg s hI e 0 i = relativePointOneBasis G hg s hI () := by
  rw [relativePointAllPoleBasis, Module.Basis.reindex_apply]

/-- Each old vector enters the next degree by the original divisor step. -/
theorem relativePointAllPoleBasis_old (m : ℕ) (i : Fin (m + 1)) :
    relativePointAllPoleBasis G hg s hI e (m + 1) i.castSucc =
      divisorPowerRingStep G.hom.appTop.hom hI (m + 1)
        (relativePointAllPoleBasis G hg s hI e m i) := by
  rw [relativePointAllPoleBasis, Module.Basis.reindex_apply, relativePoleIndexSucc_old]
  exact sectionPoleSpecifiedBasis_old _ _ _ _ _ _ _ _ _ i

/-- The last vector is the constructed actual monomial of that degree. -/
theorem relativePointAllPoleBasis_last (m : ℕ) :
    relativePointAllPoleBasis G hg s hI e (m + 1) (Fin.last (m + 1)) =
      relativePointHigherMonomial G hg s hI e m := by
  rw [relativePointAllPoleBasis, Module.Basis.reindex_apply, relativePoleIndexSucc_last]
  exact sectionPoleSpecifiedBasis_new _ _ _ _ _ _ _ _ _

end FLT.Mazur.FCurve
