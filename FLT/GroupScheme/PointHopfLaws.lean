/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PointCoalgebraLaws

/-!
# Hopf laws verified on separating points

The inverse and identity laws of a group verify the antipode identities for
integral coordinate operations. Together with the coalgebra laws this gives
a Hopf structure without assuming any of its axioms as input data.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace PointCoalgebra
universe u
variable {R H Ω X : Type u} [CommRing R] [CommRing H] [CommRing Ω]
  [Algebra R H] [Algebra R Ω] [AddGroup X]
  (e : X → H →ₐ[R] Ω)
  (hsep : ∀ {x y : H}, (∀ P, e P x = e P y) → x = y)

include hsep in
/-- Integral inversion satisfies the left antipode identity. -/
theorem antipode_left (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R) (a : H →ₐ[R] H)
    (hd : ∀ f P Q, pair e P Q (d f) = e (P + Q) f)
    (hc : ∀ f, algebraMap R Ω (c f) = e 0 f)
    (ha : ∀ f P, e P (a f) = e (-P) f) :
    (Algebra.TensorProduct.lift a (.id R H) (fun _ _ ↦ .all _ _)).comp d =
      (Algebra.ofId R H).comp c := by
  have hh (P : X) (z : H ⊗[R] H) :
      e P (Algebra.TensorProduct.lift a (.id R H) (fun _ _ ↦ .all _ _) z) =
        pair e (-P) P z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [pair, ha]
    | add x y hx hy => simp [hx, hy]
  apply AlgHom.ext
  intro f
  apply hsep
  intro P
  change e P (Algebra.TensorProduct.lift a (.id R H) (fun _ _ ↦ .all _ _) (d f)) =
    e P (algebraMap R H (c f))
  rw [AlgHom.commutes, hh, hd, neg_add_cancel, hc]

include hsep in
/-- Integral inversion satisfies the right antipode identity. -/
theorem antipode_right (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R) (a : H →ₐ[R] H)
    (hd : ∀ f P Q, pair e P Q (d f) = e (P + Q) f)
    (hc : ∀ f, algebraMap R Ω (c f) = e 0 f)
    (ha : ∀ f P, e P (a f) = e (-P) f) :
    (Algebra.TensorProduct.lift (.id R H) a (fun _ _ ↦ .all _ _)).comp d =
      (Algebra.ofId R H).comp c := by
  have hh (P : X) (z : H ⊗[R] H) :
      e P (Algebra.TensorProduct.lift (.id R H) a (fun _ _ ↦ .all _ _) z) =
        pair e P (-P) z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [pair, ha]
    | add x y hx hy => simp [hx, hy]
  apply AlgHom.ext
  intro f
  apply hsep
  intro P
  change e P (Algebra.TensorProduct.lift (.id R H) a (fun _ _ ↦ .all _ _) (d f)) =
    e P (algebraMap R H (c f))
  rw [AlgHom.commutes, hh, hd, add_neg_cancel, hc]

/-- A Hopf structure is determined by operations agreeing with a separating group of points. -/
@[instance_reducible]
def hopf
    (htriple : ∀ {x y : H ⊗[R] (H ⊗[R] H)},
      (∀ P Q S, triple e P Q S x = triple e P Q S y) → x = y)
    (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R) (a : H →ₐ[R] H)
    (hd : ∀ f P Q, pair e P Q (d f) = e (P + Q) f)
    (hc : ∀ f, algebraMap R Ω (c f) = e 0 f)
    (ha : ∀ f P, e P (a f) = e (-P) f) : HopfAlgebra R H := by
  let : Bialgebra R H := Bialgebra.ofAlgHom d c (comul_coassoc e htriple d hd)
    (counit_left e hsep d c hd hc) (counit_right e hsep d c hd hc)
  exact HopfAlgebra.ofAlgHom a (antipode_left e hsep d c a hd hc ha)
    (antipode_right e hsep d c a hd hc ha)

end PointCoalgebra
