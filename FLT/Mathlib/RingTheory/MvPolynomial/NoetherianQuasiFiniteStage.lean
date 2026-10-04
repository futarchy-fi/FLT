/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Localization.QuasiFiniteImageCover
public import FLT.Mathlib.RingTheory.MvPolynomial.QuasiFiniteCertificateStage
public import Mathlib.RingTheory.Polynomial.Basic

/-! # Eventual quasi-finiteness at a Noetherian coefficient stage -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

universe u
variable {R : Type u} {σ : Type} {ι : Type*} [CommRing R] [Finite σ] [Finite ι]

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-finite finite relation quotient over an arbitrary base has a Noetherian
coefficient model which is itself quasi-finite. The polynomial lifts retain their identities. -/
theorem exists_noetherian_quasiFinite_stage (f : ι → MvPolynomial σ R)
    [Algebra.QuasiFinite R (MvPolynomial σ R ⧸ Ideal.span (Set.range f))] :
    ∃ T : Subalgebra ℤ R, T.FG ∧ IsNoetherianRing T ∧
      ∃ g : ι → MvPolynomial σ T, (∀ i, map T.val.toRingHom (g i) = f i) ∧
        Algebra.QuasiFinite T (MvPolynomial σ T ⧸ Ideal.span (Set.range g)) := by
  classical
  obtain ⟨S, hS, _, g, hg⟩ := exists_noetherian_coefficient_stage f
  have hgf : (fun i ↦ map (algebraMap S R) (g i)) = f := funext hg
  have hq : Algebra.QuasiFinite R (MvPolynomial σ R ⧸
      Ideal.span (Set.range fun i ↦ map (algebraMap S R) (g i))) := by
    exact (Algebra.QuasiFinite.iff_of_algEquiv (Ideal.quotientEquivAlgOfEq R
      (congrArg Ideal.span (congrArg Set.range hgf)))).mpr inferInstance
  have : Algebra.QuasiFinite R
      (R ⊗[S] (MvPolynomial σ S ⧸ Ideal.span (Set.range g))) :=
    (Algebra.QuasiFinite.iff_of_algEquiv (relationBaseChangeEquiv g)).mpr hq
  obtain ⟨t, a, ha, hspan⟩ := Algebra.exists_finite_quasiFinite_image_cover
    (R := S) (S := R) (A := MvPolynomial σ S ⧸ Ideal.span (Set.range g))
  choose b hb using fun i ↦ Ideal.Quotient.mk_surjective (a i)
  have hgood (i : t) : Algebra.QuasiFinite S
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range g)) (b i))) := by
    rw [hb]
    exact ha i
  have hcover : Ideal.span (Set.range fun j ↦ Ideal.Quotient.mk
      (Ideal.span (Set.range fun i ↦ map S.val.toRingHom (g i)))
      (map S.val.toRingHom (b j))) = ⊤ := by
    have he (i : t) : relationBaseChangeEquiv (S := R) g
        ((Algebra.TensorProduct.includeRight : _ →ₐ[S] R ⊗[S] _) (a i)) =
        Ideal.Quotient.mk _ (map S.val.toRingHom (b i)) := by
      rw [← hb i]
      exact relationBaseChangeEquiv_one_tmul_mk g (b i)
    have hm := congrArg (Ideal.map (relationBaseChangeEquiv (S := R) g).toRingHom) hspan
    rw [Ideal.map_span, ← Set.range_comp, Ideal.map_top] at hm
    have hm' : Ideal.span (Set.range fun i : t ↦ relationBaseChangeEquiv (S := R) g
        ((Algebra.TensorProduct.includeRight : _ →ₐ[S] R ⊗[S] _) (a i))) = ⊤ := hm
    simp_rw [he] at hm'
    exact hm'
  obtain ⟨T, hST, hT, hN, hQ⟩ :=
    exists_quasiFinite_stage_of_principal_cover S hS g b hcover hgood
  refine ⟨T, hT, hN, fun i ↦ map (Subalgebra.inclusion hST).toRingHom (g i),
    fun i ↦ ?_, hQ⟩
  rw [map_map]
  exact hg i

end MvPolynomial
