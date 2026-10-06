/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionDifferentials
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Smooth.Fiber

/-! # Étale coordinate algebras over field fibers -/

@[expose] public noncomputable section
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- An integer annihilating differentials still annihilates them after arbitrary base change. -/
theorem kaehler_baseChange_nsmul (A S : Type u) [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (n : ℕ)
    (h : ∀ ω : KaehlerDifferential R A, n • ω = 0)
    (ω : KaehlerDifferential S (S ⊗[R] A)) : n • ω = 0 := by
  let : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let e := KaehlerDifferential.tensorKaehlerEquivBase R S A (S ⊗[R] A)
  obtain ⟨x, rfl⟩ := e.surjective ω
  have hx : n • x = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul s ω =>
      change n • (TensorProduct.mk R S (KaehlerDifferential R A) s ω) = 0
      rw [← map_nsmul, h, map_zero]
    | add x y hx hy => simp only [smul_add, hx, hy, add_zero]
  rw [← map_nsmul, hx, map_zero]

variable (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- A field fiber is étale whenever n is invertible in that field.
Invertibility in the integral coefficient ring is not required. -/
theorem torsionCoordinate_field_etale (n : ℕ) [NeZero n]
    (K : Type u) [Field K] [Algebra R K] (hn : IsUnit (n : K)) :
    Algebra.Etale K (K ⊗[R] torsionCoordinateRing W n) := by
  have : Module.Finite R (torsionCoordinateRing W n) := torsionCoordinateRing_finite W n
  have : Algebra.FormallyUnramified K (K ⊗[R] torsionCoordinateRing W n) := by
    constructor
    apply subsingleton_of_forall_eq 0
    intro ω
    apply hn.smul_eq_zero.mp
    simpa only [Nat.cast_smul_eq_nsmul] using
      kaehler_baseChange_nsmul (torsionCoordinateRing W n) K n
        (torsionCoordinateDifferential_nsmul W n) ω
  have : Algebra.FinitePresentation K (K ⊗[R] torsionCoordinateRing W n) :=
    (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

end WeierstrassCurve.CubicCharts
