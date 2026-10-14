/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointAllPoleBasis
public import FLT.Mazur.PolygonCompletePointSectionFree
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Original monomial sections on every affine Cartesian family

The canonical section comparison transports the actual monomial basis through
arbitrary affine base change, including nonreduced coefficient schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback IncreasingCechCoefficients Chow
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)

/-- The monomial H0 basis as actual global sections with the original base action. -/
def completePointMonomialSectionBasis (m : ℕ) :
    Module.Basis (Fin (m + 1)) Γ(Spec (.of (PowerSeries K)), ⊤)
      (baseSections (tensorPower (completePointLine K n h i) (m + 1))
        (exactVeroneseProjToBase K n h).appTop.hom ⊤) :=
  (completePointAllPoleBasis K n h i m).map
    (ringHZeroBaseSections _ (exactVeroneseProjToBase K n h).appTop.hom)

variable {T Y : Scheme} [IsAffine T] (a : T ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ T)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) a)

/-- Every affine Cartesian family has the basis pulled from the original monomials. -/
def completePointChangedMonomialBasis (m : ℕ) :
    Module.Basis (Fin (m + 1)) Γ(T, ⊤)
      (baseSections ((Scheme.Modules.pullback p).obj
        (tensorPower (completePointLine K n h i) (m + 1))) q.appTop.hom ⊤) := by
  letI : Algebra Γ(Spec (.of (PowerSeries K)), ⊤) Γ(T, ⊤) := a.appTop.hom.toAlgebra
  exact ((completePointMonomialSectionBasis K n h i m).baseChange Γ(T, ⊤)).map
    (completePointPowerSectionsEquiv K n h a p q hs i m)

/-- Each changed vector is the actual adjunction-unit pullback of the original monomial. -/
theorem completePointChangedMonomialBasis_apply (m : ℕ) (j : Fin (m + 1)) :
    completePointChangedMonomialBasis K n h i a p q hs m j =
      (show baseSections ((Scheme.Modules.pullback p).obj
        (tensorPower (completePointLine K n h i) (m + 1))) q.appTop.hom ⊤ from
          pullGlobal p _ (completePointMonomialSectionBasis K n h i m j)) := by
  let _ : Algebra Γ(Spec (.of (PowerSeries K)), ⊤) Γ(T, ⊤) := a.appTop.hom.toAlgebra
  rw [completePointChangedMonomialBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    completePointPowerSectionsEquiv_tmul, one_smul]

end FLT.Mazur.PolygonInfinitesimalStages
