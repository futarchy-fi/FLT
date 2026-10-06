/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionDifferentials
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Unramified invertible-order torsion of the actual cubic group -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- The actual torsion kernel is formally unramified when its order is invertible. -/
theorem torsionModel_formallyUnramified (n : ℕ) [NeZero n]
    (hn : IsUnit (n : R)) : FormallyUnramified (torsionModel W n).hom := by
  have hf : FormallyUnramified (Spec.map (CommRingCat.ofHom
      (algebraMap R (torsionCoordinateRing W n)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    change (algebraMap R (torsionCoordinateRing W n)).FormallyUnramified
    rw [RingHom.formallyUnramified_algebraMap]
    exact torsionCoordinate_formallyUnramified W n hn
  change FormallyUnramified (Scheme.Spec.map (Spec.fullyFaithful.preimage
    ((torsionModel W n).left.isoSpec.inv ≫ (torsionModel W n).hom))) at hf
  rw [Spec.fullyFaithful.map_preimage] at hf
  exact (MorphismProperty.cancel_left_of_respectsIso @FormallyUnramified
    (torsionModel W n).left.isoSpec.inv (torsionModel W n).hom).mp hf

end WeierstrassCurve.CubicCharts
