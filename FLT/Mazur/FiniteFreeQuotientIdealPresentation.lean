/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartIdealPresentation
public import FLT.Mazur.IdealPresentationQuotient
public import Mathlib.RingTheory.FinitePresentation

/-!
# Ideal finite presentation from a finite free quotient

Add lifts of a quotient basis to a finite polynomial presentation of the
ambient algebra. The enlarged polynomial quotient belongs to an integer
Hilbert chart with basis polynomials that are single variables. Its ideal is
finitely presented over the arbitrary coefficient ring. Quotienting by the
ambient's finitely many relations proves finite presentation of the original
ideal. No Noetherian assumption on the coefficient ring is needed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Algebra.FinitePresentation R B]

/-- A finite basis of the quotient supplies finite presentation of its entire ideal. -/
theorem ideal_finitePresentation_of_quotient_basis (I : Ideal B) {d : ℕ}
    (v : Module.Basis (Fin d) R (B ⧸ I)) : Module.FinitePresentation B I := by
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)
  choose y hy using fun i ↦ Ideal.Quotient.mk_surjective (v i)
  let z : Fin n ⊕ Fin d → B := Sum.elim (fun i ↦ π (MvPolynomial.X i)) y
  let p : MvPolynomial (Fin n ⊕ Fin d) R →ₐ[R] B := MvPolynomial.aeval z
  have hpπ : p.comp (MvPolynomial.rename Sum.inl) = π := by
    ext i
    simp [p, z]
  have hp : Function.Surjective p := by
    intro b
    obtain ⟨a, rfl⟩ := hπ b
    exact ⟨MvPolynomial.rename Sum.inl a, AlgHom.congr_fun hpπ a⟩
  let q : B →ₐ[R] B ⧸ I := Ideal.Quotient.mkₐ R I
  let x : Fin n ⊕ Fin d → B ⧸ I := fun i ↦ q (z i)
  have hqp : q.comp p = MvPolynomial.aeval x := by
    ext i
    simp [p, x]
  let J := I.comap p.toRingHom
  have hw (i : Fin d) :
      MvPolynomial.aeval x (MvPolynomial.X (Sum.inr i) :
        MvPolynomial (Fin n ⊕ Fin d) ℤ) = v i := by
    simpa [x, z, q] using hy i
  have hJ : J = RingHom.ker
      (MvPolynomial.aeval x : MvPolynomial (Fin n ⊕ Fin d) R →ₐ[R] B ⧸ I).toRingHom := by
    ext a
    change p a ∈ I ↔ MvPolynomial.aeval x a = 0
    rw [← hqp]
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  let _ : Module.FinitePresentation (MvPolynomial (Fin n ⊕ Fin d) R) J := by
    rw [hJ]
    exact HilbertChart.evaluation_ker_finitePresentation_of_basis
      ℤ (Fin n ⊕ Fin d) d (fun i ↦ MvPolynomial.X (Sum.inr i)) v x hw
  have hker : (RingHom.ker p.toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective p hp
  have hle : RingHom.ker p.toRingHom ≤ J := by
    intro a ha
    change p a ∈ I
    rw [show p a = 0 from ha]
    exact I.zero_mem
  have h := ideal_finitePresentation_map_surjective p.toRingHom hp J hker hle
  have hJI : J.map p.toRingHom = I := by
    change (I.comap p.toRingHom).map p.toRingHom = I
    exact Ideal.map_comap_of_surjective p.toRingHom hp I
  rwa [hJI] at h

end FLT.Mazur.FCurve
