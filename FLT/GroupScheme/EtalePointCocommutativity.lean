/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.EtalePointHopf

/-!
# Cocommutativity detected on generic points

Commutative addition on a complete set of generic points forces the integral
comultiplication to be cocommutative, by flatness and generic etaleness.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace PointCoalgebra
universe u
variable {R K Ω H X : Type u} [CommRing R] [Field K] [Field Ω]
  [CommRing H] [Bialgebra R H] [Algebra R K] [Algebra R Ω] [Algebra K Ω]
  [IsScalarTower R K Ω] [IsFractionRing R K] [IsGalois K Ω] [IsSepClosed Ω]
  [Module.Flat R H] [Algebra.Etale K (K ⊗[R] H)] [AddCommGroup X]
  (e : X → H →ₐ[R] Ω) (he : Function.Surjective e)

include K he in
/-- A commutative group law on generic points implies integral cocommutativity. -/
theorem isCocomm_of_points
    (hd : ∀ f P Q, pair e P Q (Coalgebra.comul (R := R) f) = e (P + Q) f) :
    Coalgebra.IsCocomm R H := by
  constructor
  ext x
  let := Algebra.etale_genericFiber_tensorSquare R K H
  apply Algebra.eq_of_generic_points_eq R K Ω (H ⊗[R] H)
  intro f
  obtain ⟨⟨P, Q⟩, rfl⟩ := pair_surjective e he f
  have hh (z : H ⊗[R] H) : pair e P Q (TensorProduct.comm R H H z) = pair e Q P z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [pair, mul_comm]
    | add a b ha hb => simp only [map_add, ha, hb]
  change pair e P Q (TensorProduct.comm R H H (Coalgebra.comul x)) =
    pair e P Q (Coalgebra.comul x)
  rw [hh, hd, hd, add_comm]

end PointCoalgebra
