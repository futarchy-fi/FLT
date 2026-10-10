/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePolynomialDiagramCoefficients
public import FLT.Mazur.NoetherianRelationContraction
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Simultaneous finite relation closure in polynomial diagrams

Choose one finitely generated ideal at each vertex, containing any prescribed
finite relations and preserved by every arrow. No acyclicity is needed, and
the original relation ideals need not be finitely generated.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {E : Type w} [Finite E] (n : ι → ℕ) (src dst : E → ι)

/-- Finite relations close at one simultaneous stage, including along cyclic arrows. -/
theorem exists_stable_relations
    (f : ∀ e, MvPolynomial (Fin (n (src e))) R →ₐ[R]
      MvPolynomial (Fin (n (dst e))) R)
    (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
    (hf : ∀ e, I (src e) ≤ (I (dst e)).comap (f e).toRingHom)
    (s : ∀ i, Finset (MvPolynomial (Fin (n i)) R))
    (hs : ∀ i, (s i : Set (MvPolynomial (Fin (n i)) R)) ⊆ I i) :
    ∃ J : ∀ i, Ideal (MvPolynomial (Fin (n i)) R),
      (∀ i, (J i).FG) ∧ (∀ i, Ideal.span (s i : Set _) ≤ J i) ∧
      (∀ i, J i ≤ I i) ∧
      ∀ e, J (src e) ≤ (J (dst e)).comap (f e).toRingHom := by
  obtain ⟨S, hS, hsS, f₀, hcomm⟩ := exists_diagram_coefficients n src dst f s
  let _ := hS
  let c (i) := MvPolynomial.map (σ := Fin (n i)) S.subtype
  let J (i) := NoetherianRelationContraction.relations (c i) (I i)
  refine ⟨J, fun i ↦ NoetherianRelationContraction.relations_fg (c i) (I i),
    fun i ↦ NoetherianRelationContraction.span_le_relations (c i) (I i) _ (hs i) (hsS i),
    fun i ↦ NoetherianRelationContraction.relations_le (c i) (I i), fun e ↦ ?_⟩
  apply Ideal.map_le_iff_le_comap.mp
  exact NoetherianRelationContraction.map_relations_le (c (src e)) (I (src e))
    (c (dst e)) (I (dst e)) (f e).toRingHom (f₀ e).toRingHom (hcomm e) (hf e)

end FLT.Mazur.FinitePolynomialCoefficients
