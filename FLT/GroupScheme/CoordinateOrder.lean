/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.EtaleOrder
/-!
# Hopf structures on integral algebras of functions

Addition, zero and inversion on a group determine Hopf operations whenever
they preserve its coordinate order. Étale generic points verify coassociativity;
flatness then gives the equality over the coefficient ring.
-/

@[expose] public section

set_option maxSynthPendingDepth 8
open scoped TensorProduct
universe u
namespace CoordinateOrder
variable {R K k X : Type u} [CommRing R] [Field K] [Field k]
    [Algebra R K] [Algebra R k] [Algebra K k] [IsScalarTower R K k]
    [IsFractionRing R K] [IsGalois K k] [IsSepClosed k] [AddCommGroup X]
    (H : Subalgebra R (X → k))
omit [Field K] [Algebra R K] [Algebra K k] [IsScalarTower R K k]
    [IsFractionRing R K] [IsGalois K k] [IsSepClosed k] in
/-- Evaluate a coordinate function at a group element. -/
def evaluation (P : X) : H →ₐ[R] k := (Pi.evalAlgHom R _ P).comp H.val
omit [Field K] [Algebra R K] [Algebra K k] [IsScalarTower R K k]
    [IsFractionRing R K] [IsGalois K k] [IsSepClosed k] in
/-- Evaluate a tensor of coordinate functions at a pair of group elements. -/
def pair (P Q : X) : (H ⊗[R] H) →ₐ[R] k :=
  Algebra.TensorProduct.lift (evaluation H P) (evaluation H Q) (fun _ _ => Commute.all _ _)
omit [Field K] [Algebra R K] [Algebra K k] [IsScalarTower R K k]
    [IsFractionRing R K] [IsGalois K k] [IsSepClosed k] in
/-- Evaluate the right-associated tensor cube on three group elements. -/
def triple (P Q S : X) : (H ⊗[R] (H ⊗[R] H)) →ₐ[R] k :=
  Algebra.TensorProduct.lift (evaluation H P) (pair H Q S) (fun _ _ => Commute.all _ _)

omit [IsSepClosed k] [AddCommGroup X] in
/-- Evaluate a tensor of coordinate functions at a pair of group elements. -/
theorem pair_points (he : Function.Surjective (evaluation H)) (f : (H ⊗[R] H) →ₐ[R] k) :
    ∃ P Q, f = pair H P Q := by
  obtain ⟨P, hp⟩ := he (f.comp Algebra.TensorProduct.includeLeft)
  obtain ⟨Q, hq⟩ := he (f.comp Algebra.TensorProduct.includeRight)
  refine ⟨P, Q, ?_⟩
  apply Algebra.TensorProduct.ext
  · ext a
    exact (DFunLike.congr_fun hp a).symm.trans (by simp [pair])
  · ext a
    exact (DFunLike.congr_fun hq a).symm.trans (by simp [pair])

omit [IsSepClosed k] [AddCommGroup X] in
/-- Evaluate the right-associated tensor cube on three group elements. -/
theorem triple_points (he : Function.Surjective (evaluation H))
    (f : (H ⊗[R] (H ⊗[R] H)) →ₐ[R] k) : ∃ P Q S, f = triple H P Q S := by
  obtain ⟨P, hp⟩ := he (f.comp Algebra.TensorProduct.includeLeft)
  obtain ⟨Q, S, hq⟩ := pair_points H he (f.comp Algebra.TensorProduct.includeRight)
  refine ⟨P, Q, S, ?_⟩
  apply Algebra.TensorProduct.ext
  · ext a
    exact (DFunLike.congr_fun hp a).symm.trans (by simp [triple])
  · apply AlgHom.ext
    intro a
    exact (DFunLike.congr_fun hq a).trans (by simp [triple])

omit [IsFractionRing R K] in
/-- Tensor products preserve an étale generic fibre. -/
theorem etale_tensor (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale K (K ⊗[R] A)] [Algebra.Etale K (K ⊗[R] B)] :
    Algebra.Etale K (K ⊗[R] (A ⊗[R] B)) := by
  let e : ((K ⊗[R] A) ⊗[K] (K ⊗[R] B)) ≃ₐ[K] K ⊗[R] (A ⊗[R] B) :=
    (Algebra.TensorProduct.tensorTensorTensorComm R R K K K A K B).trans
      (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid K K)
        (AlgEquiv.refl : (A ⊗[R] B) ≃ₐ[R] (A ⊗[R] B)))
  let : Algebra.Etale K ((K ⊗[R] A) ⊗[K] (K ⊗[R] B)) :=
    Algebra.Etale.comp K (K ⊗[R] A) ((K ⊗[R] A) ⊗[K] (K ⊗[R] B))
  exact Algebra.Etale.of_equiv e

omit [AddCommGroup X] in
/-- Evaluate the right-associated tensor cube on three group elements. -/
theorem triple_separates [Module.Flat R H] [Algebra.Etale K (K ⊗[R] H)]
    (he : Function.Surjective (evaluation H)) {x y : H ⊗[R] (H ⊗[R] H)}
    (h : ∀ P Q S, triple H P Q S x = triple H P Q S y) : x = y := by
  let : Algebra.Etale K (K ⊗[R] (H ⊗[R] H)) := Algebra.etale_genericFiber_tensorSquare R K H
  let : Algebra.Etale K (K ⊗[R] (H ⊗[R] (H ⊗[R] H))) :=
    etale_tensor (R := R) (K := K) H (H ⊗[R] H)
  apply Algebra.eq_of_generic_points_eq R K k (H ⊗[R] (H ⊗[R] H))
  intro f
  obtain ⟨P, Q, S, rfl⟩ := triple_points H he f
  exact h P Q S

omit [IsSepClosed k] [AddCommGroup X] in
/-- Evaluate the right-associated tensor cube on three group elements. -/
theorem triple_assoc_tmul (P Q S : X) (z : H ⊗[R] H) (f : H) :
    triple H P Q S ((Algebra.TensorProduct.assoc R R R H H H) (z ⊗ₜ[R] f)) =
      pair H P Q z * f.val S := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [triple, pair, evaluation, mul_assoc]
  | add a b ha hb => simp [TensorProduct.add_tmul, ha, hb, add_mul]

/-- Integral coaddition is coassociative because group addition is associative. -/
theorem comul_coassoc [Module.Flat R H] [Algebra.Etale K (K ⊗[R] H)]
    (he : Function.Surjective (evaluation H)) (d : H →ₐ[R] H ⊗[R] H)
    (hd : ∀ f P Q, pair H P Q (d f) = f.val (P + Q)) :
    (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
      ((Algebra.TensorProduct.map d (.id R H)).comp d) =
        (Algebra.TensorProduct.map (.id R H) d).comp d := by
  have hl (P Q S : X) (z : H ⊗[R] H) :
      triple H P Q S ((Algebra.TensorProduct.assoc R R R H H H)
        (Algebra.TensorProduct.map d (.id R H) z)) = pair H (P + Q) S z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, triple_assoc_tmul, hd]
      simp [pair, evaluation]
    | add a b ha hb => simp [ha, hb]
  have hr (P Q S : X) (z : H ⊗[R] H) :
      triple H P Q S (Algebra.TensorProduct.map (.id R H) d z) = pair H P (Q + S) z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change (evaluation H P a) * (pair H Q S (d b)) = pair H P (Q + S) (a ⊗ₜ[R] b)
      rw [hd]
      simp [pair, evaluation]
    | add a b ha hb => simp [ha, hb]
  apply AlgHom.ext
  intro f
  apply triple_separates (K := K) H he
  intro P Q S
  change triple H P Q S ((Algebra.TensorProduct.assoc R R R H H H)
    (Algebra.TensorProduct.map d (.id R H) (d f))) =
      triple H P Q S (Algebra.TensorProduct.map (.id R H) d (d f))
  rw [hl, hr, hd, hd, add_assoc]
omit [IsSepClosed k] in
/-- Evaluation at zero is a left counit for integral coaddition. -/
theorem counit_left (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R)
    (hd : ∀ f P Q, pair H P Q (d f) = f.val (P + Q))
    (hc : ∀ f, algebraMap R k (c f) = f.val 0) :
    (Algebra.TensorProduct.map c (.id R H)).comp d =
      (Algebra.TensorProduct.lid R H).symm := by
  have hh (P : X) (z : H ⊗[R] H) :
      ((Algebra.TensorProduct.lid R H) (Algebra.TensorProduct.map c (.id R H) z)).val P =
        pair H 0 P z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [pair, evaluation, Algebra.smul_def, hc]
    | add a b ha hb => simp [ha, hb]
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.lid R H).injective
  change (Algebra.TensorProduct.lid R H) (Algebra.TensorProduct.map c (.id R H) (d f)) =
    (Algebra.TensorProduct.lid R H) ((Algebra.TensorProduct.lid R H).symm f)
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  funext P
  rw [hh, hd, zero_add]

omit [IsSepClosed k] in
/-- Evaluation at zero is a right counit for integral coaddition. -/
theorem counit_right (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R)
    (hd : ∀ f P Q, pair H P Q (d f) = f.val (P + Q))
    (hc : ∀ f, algebraMap R k (c f) = f.val 0) :
    (Algebra.TensorProduct.map (.id R H) c).comp d =
      (Algebra.TensorProduct.rid R R H).symm := by
  have hh (P : X) (z : H ⊗[R] H) :
      ((Algebra.TensorProduct.rid R R H) (Algebra.TensorProduct.map (.id R H) c z)).val P =
        pair H P 0 z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [pair, evaluation, Algebra.smul_def, hc, mul_comm]
    | add a b ha hb => simp [ha, hb]
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.rid R R H).injective
  change (Algebra.TensorProduct.rid R R H) (Algebra.TensorProduct.map (.id R H) c (d f)) =
    (Algebra.TensorProduct.rid R R H) ((Algebra.TensorProduct.rid R R H).symm f)
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  funext P
  rw [hh, hd, add_zero]

omit [IsSepClosed k] in
/-- Integral inversion satisfies the left antipode identity. -/
theorem antipode_left (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R) (S : H →ₐ[R] H)
    (hd : ∀ f P Q, pair H P Q (d f) = f.val (P + Q))
    (hc : ∀ f, algebraMap R k (c f) = f.val 0)
    (hs : ∀ f P, (S f).val P = f.val (-P)) :
    (Algebra.TensorProduct.lift S (.id R H) (fun _ _ => Commute.all _ _)).comp d =
      (Algebra.ofId R H).comp c := by
  have hh (P : X) (z : H ⊗[R] H) :
      (Algebra.TensorProduct.lift S (.id R H) (fun _ _ => Commute.all _ _) z).val P =
        pair H (-P) P z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [pair, evaluation, hs]
    | add a b ha hb => simp [ha, hb]
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  funext P
  change (Algebra.TensorProduct.lift S (.id R H) (fun _ _ => Commute.all _ _) (d f)).val P =
    algebraMap R k (c f)
  rw [hh, hd, neg_add_cancel, hc]

omit [IsSepClosed k] in
/-- Integral inversion satisfies the right antipode identity. -/
theorem antipode_right (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R) (S : H →ₐ[R] H)
    (hd : ∀ f P Q, pair H P Q (d f) = f.val (P + Q))
    (hc : ∀ f, algebraMap R k (c f) = f.val 0)
    (hs : ∀ f P, (S f).val P = f.val (-P)) :
    (Algebra.TensorProduct.lift (.id R H) S (fun _ _ => Commute.all _ _)).comp d =
      (Algebra.ofId R H).comp c := by
  have hh (P : X) (z : H ⊗[R] H) :
      (Algebra.TensorProduct.lift (.id R H) S (fun _ _ => Commute.all _ _) z).val P =
        pair H P (-P) z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [pair, evaluation, hs]
    | add a b ha hb => simp [ha, hb]
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  funext P
  change (Algebra.TensorProduct.lift (.id R H) S (fun _ _ => Commute.all _ _) (d f)).val P =
    algebraMap R k (c f)
  rw [hh, hd, add_neg_cancel, hc]

/-- The Hopf structure determined by integral addition, zero and inversion. -/
@[instance_reducible]
noncomputable def hopf [Module.Flat R H] [Algebra.Etale K (K ⊗[R] H)]
    (he : Function.Surjective (evaluation H))
    (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R) (S : H →ₐ[R] H)
    (hd : ∀ f P Q, pair H P Q (d f) = f.val (P + Q))
    (hc : ∀ f, algebraMap R k (c f) = f.val 0)
    (hs : ∀ f P, (S f).val P = f.val (-P)) : HopfAlgebra R H := by
  let : Bialgebra R H := Bialgebra.ofAlgHom d c
    (comul_coassoc (K := K) H he d hd) (counit_left H d c hd hc) (counit_right H d c hd hc)
  exact HopfAlgebra.ofAlgHom S (antipode_left H d c S hd hc hs) (antipode_right H d c S hd hc hs)
end CoordinateOrder
