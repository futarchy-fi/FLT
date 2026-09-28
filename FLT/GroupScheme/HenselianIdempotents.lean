/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Idempotents

/-!
# Lifting component idempotents over a Henselian pair

Idempotents lift uniquely modulo a Henselian ideal. Thus a complete orthogonal
family in the special fibre lifts to a product decomposition of the original
algebra. This is the algebraic component-lifting step of the connected–étale
construction; it does not assert compatibility with a Hopf structure.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- An idempotent in the Jacobson radical is zero. -/
theorem idempotent_eq_zero_of_mem_jacobson {e : A} (he : IsIdempotentElem e)
    (h : e ∈ (⊥ : Ideal A).jacobson) : e = 0 := by
  have hu : IsUnit (1 - e) := by
    simpa only [mul_neg_one, neg_add_eq_sub] using (Ideal.mem_jacobson_bot.mp h) (-1)
  have hz : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  exact (hu.mul_right_eq_zero).mp hz

/-- Reduction modulo a Jacobson ideal distinguishes idempotents. -/
theorem idempotent_eq_of_quotient_eq (hI : I ≤ (⊥ : Ideal A).jacobson)
    {e f : A} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : Ideal.Quotient.mk I e = Ideal.Quotient.mk I f) : e = f := by
  have hz (x y : A) (hx : IsIdempotentElem x) (hy : IsIdempotentElem y)
      (hxy : Ideal.Quotient.mk I x = Ideal.Quotient.mk I y) : x * (1 - y) = 0 := by
    apply idempotent_eq_zero_of_mem_jacobson (hx.mul hy.one_sub)
    apply hI
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_one, hxy]
    exact (hy.map (Ideal.Quotient.mk I)).mul_one_sub_self
  have h₁ := hz e f he hf h
  have h₂ := hz f e hf he h.symm
  linear_combination h₁ - h₂

/-- Every special-fibre idempotent has a unique integral lift over a Henselian pair. -/
theorem existsUnique_idempotent_lift [HenselianRing A I]
    (e : A ⧸ I) (he : IsIdempotentElem e) :
    ∃! x : A, IsIdempotentElem x ∧ Ideal.Quotient.mk I x = e := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
  let p : Polynomial A := Polynomial.X * (Polynomial.X - 1)
  have hp : p.Monic := Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1)
  have ha : p.eval a ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp [p, mul_sub, map_mul, map_sub, he.eq]
  have hd : IsUnit (Ideal.Quotient.mk I (p.derivative.eval a)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨2 * Ideal.Quotient.mk I a - 1, ?_⟩
    simp only [p, Polynomial.derivative_mul, Polynomial.derivative_X,
      Polynomial.derivative_one, sub_zero,
      Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_sub, Polynomial.eval_X, one_mul, mul_one,
      map_add, map_sub, map_one]
    linear_combination 4 * he.eq
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian p hp a ha hd
  have hxi : IsIdempotentElem x := by
    change p.eval x = 0 at hx
    simp only [p, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub,
      mul_sub, mul_one, sub_eq_zero] at hx
    exact hx
  have hxr : Ideal.Quotient.mk I x = Ideal.Quotient.mk I a :=
    Ideal.Quotient.eq.mpr hxa
  exact ⟨x, ⟨hxi, hxr⟩, fun y hy ↦
    idempotent_eq_of_quotient_eq I HenselianRing.jac hy.1 hxi (hy.2.trans hxr.symm)⟩

/-- A special-fibre decomposition lifts uniquely to complete orthogonal integral
idempotents. Orthogonality and completeness follow from uniqueness of lifting. -/
theorem existsUnique_completeOrthogonalIdempotents_lift [HenselianRing A I]
    {ι : Type*} [Fintype ι] (e : ι → A ⧸ I) (he : CompleteOrthogonalIdempotents e) :
    ∃! f : ι → A, CompleteOrthogonalIdempotents f ∧
      ∀ i, Ideal.Quotient.mk I (f i) = e i := by
  choose f hf using fun i ↦ existsUnique_idempotent_lift I (e i) (he.idem i)
  have hfi (i) : IsIdempotentElem (f i) := (hf i).1.1
  have hfr (i) : Ideal.Quotient.mk I (f i) = e i := (hf i).1.2
  have ho : OrthogonalIdempotents f := by
    refine ⟨hfi, fun i j hij ↦ ?_⟩
    apply idempotent_eq_of_quotient_eq I HenselianRing.jac ((hfi i).mul (hfi j)) .zero
    simpa only [map_mul, hfr, map_zero] using he.ortho hij
  have hc : CompleteOrthogonalIdempotents f := by
    refine ⟨ho, ?_⟩
    apply idempotent_eq_of_quotient_eq I HenselianRing.jac ho.isIdempotentElem_sum .one
    simpa only [map_sum, hfr, map_one] using he.complete
  exact ⟨f, ⟨hc, hfr⟩, fun g hg ↦ funext fun i ↦ (hf i).2 (g i) ⟨hg.1.idem i, hg.2 i⟩⟩

/-- The integral component idempotents associated with a special-fibre decomposition. -/
def henselianComponentIdempotents [HenselianRing A I]
    {ι : Type*} [Fintype ι] (e : ι → A ⧸ I) (he : CompleteOrthogonalIdempotents e) : ι → A :=
  (existsUnique_completeOrthogonalIdempotents_lift I e he).choose

/-- The lifted component idempotents are complete and orthogonal. -/
theorem henselianComponentIdempotents_complete [HenselianRing A I]
    {ι : Type*} [Fintype ι] (e : ι → A ⧸ I) (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (henselianComponentIdempotents I e he) :=
  (existsUnique_completeOrthogonalIdempotents_lift I e he).choose_spec.1.1

/-- Reduction recovers the prescribed special-fibre components. -/
@[simp] theorem henselianComponentIdempotents_reduce [HenselianRing A I]
    {ι : Type*} [Fintype ι] (e : ι → A ⧸ I) (he : CompleteOrthogonalIdempotents e) (i : ι) :
    Ideal.Quotient.mk I (henselianComponentIdempotents I e he i) = e i :=
  (existsUnique_completeOrthogonalIdempotents_lift I e he).choose_spec.1.2 i

/-- The algebra product decomposition lifted from the special fibre. -/
def henselianComponentEquiv {R : Type*} [CommRing R] [Algebra R A] [HenselianRing A I]
    {ι : Type*} [Fintype ι] (e : ι → A ⧸ I) (he : CompleteOrthogonalIdempotents e) :
    A ≃ₐ[R] Π i, A ⧸ Ideal.span {1 - henselianComponentIdempotents I e he i} :=
  AlgEquiv.ofBijective (AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ R
    (Ideal.span {1 - henselianComponentIdempotents I e he i}))
    (henselianComponentIdempotents_complete I e he).bijective_pi

end ThreeAdicPlan
