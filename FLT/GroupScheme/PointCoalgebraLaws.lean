/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.EtaleOrder

/-!
# Coalgebra laws verified on separating points

An algebra whose points separate its elements and tensor cube inherits the
coalgebra laws from an associative group law. This is a verification theorem,
not an assumed coalgebra structure.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace PointCoalgebra
universe u
variable {R H Ω X : Type u} [CommRing R] [CommRing H] [CommRing Ω]
  [Algebra R H] [Algebra R Ω] [AddGroup X]
  (e : X → H →ₐ[R] Ω)

/-- Evaluate two tensor coordinates at two points. -/
def pair (P Q : X) : H ⊗[R] H →ₐ[R] Ω :=
  Algebra.TensorProduct.lift (e P) (e Q) (fun _ _ ↦ .all _ _)

/-- Evaluate three tensor coordinates at three points. -/
def triple (P Q S : X) : H ⊗[R] (H ⊗[R] H) →ₐ[R] Ω :=
  Algebra.TensorProduct.lift (e P) (pair e Q S) (fun _ _ ↦ .all _ _)

omit [AddGroup X] in
/-- Evaluate the right-associated tensor cube on three group elements. -/
theorem triple_assoc_tmul (P Q S : X) (z : H ⊗[R] H) (f : H) :
    triple e P Q S ((Algebra.TensorProduct.assoc R R R H H H) (z ⊗ₜ[R] f)) =
      pair e P Q z * e S f := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [triple, pair, mul_assoc]
  | add a b ha hb => simp [TensorProduct.add_tmul, ha, hb, add_mul]

/-- Integral coaddition is coassociative because group addition is associative. -/
theorem comul_coassoc (htriple : ∀ {x y : H ⊗[R] (H ⊗[R] H)},
      (∀ P Q S, triple e P Q S x = triple e P Q S y) → x = y) (d : H →ₐ[R] H ⊗[R] H)
    (hd : ∀ f P Q, pair e P Q (d f) = e (P + Q) f) :
    (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
      ((Algebra.TensorProduct.map d (.id R H)).comp d) =
        (Algebra.TensorProduct.map (.id R H) d).comp d := by
  have hl (P Q S : X) (z : H ⊗[R] H) :
      triple e P Q S ((Algebra.TensorProduct.assoc R R R H H H)
        (Algebra.TensorProduct.map d (.id R H) z)) = pair e (P + Q) S z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, triple_assoc_tmul, hd]
      simp [pair]
    | add a b ha hb => simp [ha, hb]
  have hr (P Q S : X) (z : H ⊗[R] H) :
      triple e P Q S (Algebra.TensorProduct.map (.id R H) d z) = pair e P (Q + S) z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change (e P a) * (pair e Q S (d b)) = pair e P (Q + S) (a ⊗ₜ[R] b)
      rw [hd]
      simp [pair]
    | add a b ha hb => simp [ha, hb]
  apply AlgHom.ext
  intro f
  apply htriple
  intro P Q S
  change triple e P Q S ((Algebra.TensorProduct.assoc R R R H H H)
    (Algebra.TensorProduct.map d (.id R H) (d f))) =
      triple e P Q S (Algebra.TensorProduct.map (.id R H) d (d f))
  rw [hl, hr, hd, hd, add_assoc]
/-- Evaluation at zero is a left counit for integral coaddition. -/
theorem counit_left
    (hsep : ∀ {x y : H}, (∀ P, e P x = e P y) → x = y) (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R)
    (hd : ∀ f P Q, pair e P Q (d f) = e (P + Q) f)
    (hc : ∀ f, algebraMap R Ω (c f) = e 0 f) :
    (Algebra.TensorProduct.map c (.id R H)).comp d =
      (Algebra.TensorProduct.lid R H).symm := by
  have hh (P : X) (z : H ⊗[R] H) :
      e P ((Algebra.TensorProduct.lid R H) (Algebra.TensorProduct.map c (.id R H) z)) =
        pair e 0 P z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [pair, Algebra.smul_def, hc]
    | add a b ha hb => simp [ha, hb]
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.lid R H).injective
  change (Algebra.TensorProduct.lid R H) (Algebra.TensorProduct.map c (.id R H) (d f)) =
    (Algebra.TensorProduct.lid R H) ((Algebra.TensorProduct.lid R H).symm f)
  rw [AlgEquiv.apply_symm_apply]
  apply hsep
  intro P
  rw [hh, hd, zero_add]

/-- Evaluation at zero is a right counit for integral coaddition. -/
theorem counit_right
    (hsep : ∀ {x y : H}, (∀ P, e P x = e P y) → x = y) (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R)
    (hd : ∀ f P Q, pair e P Q (d f) = e (P + Q) f)
    (hc : ∀ f, algebraMap R Ω (c f) = e 0 f) :
    (Algebra.TensorProduct.map (.id R H) c).comp d =
      (Algebra.TensorProduct.rid R R H).symm := by
  have hh (P : X) (z : H ⊗[R] H) :
      e P ((Algebra.TensorProduct.rid R R H) (Algebra.TensorProduct.map (.id R H) c z)) =
        pair e P 0 z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [pair, Algebra.smul_def, hc, mul_comm]
    | add a b ha hb => simp [ha, hb]
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.rid R R H).injective
  change (Algebra.TensorProduct.rid R R H) (Algebra.TensorProduct.map (.id R H) c (d f)) =
    (Algebra.TensorProduct.rid R R H) ((Algebra.TensorProduct.rid R R H).symm f)
  rw [AlgEquiv.apply_symm_apply]
  apply hsep
  intro P
  rw [hh, hd, add_zero]


end PointCoalgebra
