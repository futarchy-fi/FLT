/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointSectionBaseChange
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Free section modules over the original complete base

The actual positive point-power sections are finite projective over a local
ring, hence free. Their bases extend through the canonical section comparison
on every affine Cartesian square.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback IncreasingCechCoefficients Chow

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Functions on the original complete coefficient base form a local ring. -/
theorem completeBase_sections_local : IsLocalRing Γ(Spec (.of (PowerSeries K)), ⊤) :=
  (Scheme.ΓSpecIso (.of (PowerSeries K))).commRingCatIsoToRingEquiv.symm.isLocalRing

/-- Positive point-power sections are free over the original complete base. -/
theorem completePointPower_sections_free (i : Fin n) (m : ℕ) :
    Module.Free Γ(Spec (.of (PowerSeries K)), ⊤)
      (baseSections (tensorPower (completePointLine K n h i) (m + 1))
        (exactVeroneseProjToBase K n h).appTop.hom ⊤) := by
  let _ := completeBase_sections_local K
  let _ := completePointPower_sections_finite K n h i m
  let _ := completePointPower_sections_projective K n h i m
  let _ : Module.Flat Γ(Spec (.of (PowerSeries K)), ⊤)
      (baseSections (tensorPower (completePointLine K n h i) (m + 1))
        (exactVeroneseProjToBase K n h).appTop.hom ⊤) := Module.Flat.of_projective
  exact Module.free_of_flat_of_isLocalRing

variable {S Y : Scheme} [IsAffine S] (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The actual canonical section map as an equivalence, with no choice of coordinates. -/
def completePointPowerSectionsEquiv (i : Fin n) (m : ℕ) :
    let _ : Algebra Γ(Spec (.of (PowerSeries K)), ⊤) Γ(S, ⊤) := s.appTop.hom.toAlgebra
    Γ(S, ⊤) ⊗[Γ(Spec (.of (PowerSeries K)), ⊤)]
      (baseSections (tensorPower (completePointLine K n h i) (m + 1))
        (exactVeroneseProjToBase K n h).appTop.hom ⊤) ≃ₗ[Γ(S, ⊤)]
      baseSections ((Scheme.Modules.pullback p).obj
        (tensorPower (completePointLine K n h i) (m + 1))) q.appTop.hom ⊤ :=
  LinearEquiv.ofBijective _ (completePointPower_globalComparison_bijective K n h s p q hs i m)

/-- Pure tensors still map to the original adjunction-unit pullback of sections. -/
theorem completePointPowerSectionsEquiv_tmul (i : Fin n) (m : ℕ) (b : Γ(S, ⊤))
    (v : baseSections (tensorPower (completePointLine K n h i) (m + 1))
      (exactVeroneseProjToBase K n h).appTop.hom ⊤) :
    let _ : Algebra Γ(Spec (.of (PowerSeries K)), ⊤) Γ(S, ⊤) := s.appTop.hom.toAlgebra
    completePointPowerSectionsEquiv K n h s p q hs i m
      (b ⊗ₜ[Γ(Spec (.of (PowerSeries K)), ⊤)] v) =
      b • (show baseSections ((Scheme.Modules.pullback p).obj
        (tensorPower (completePointLine K n h i) (m + 1))) q.appTop.hom ⊤ from
          pullGlobal p _ v) :=
  globalComparison_tmul hs _ b v

end FLT.Mazur.PolygonInfinitesimalStages
