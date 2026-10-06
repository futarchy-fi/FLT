/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Étale field fibers of invertible-order torsion -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- Field fibers of invertible-order torsion are étale, without assuming integral flatness. -/
theorem torsionModel_fieldFiber_etale (n : ℕ) [NeZero n] (hn : IsUnit (n : R))
    (K : Type u) [Field K] [Algebra R K] :
    Etale (pullback.snd (torsionModel W n).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  have h := torsionModel_formallyUnramified W n hn
  have : FormallyUnramified (pullback.snd (torsionModel W n).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    MorphismProperty.pullback_snd _ _ h
  exact Etale.of_formallyUnramified_of_flat _

end WeierstrassCurve.CubicCharts
