/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePolynomialCoefficientRing
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# Common coefficients for a finite polynomial diagram

All arrow maps and all prescribed relations descend to one Noetherian
coefficient subring. The diagram may contain loops and parallel arrows.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {E : Type w} [Finite E] (n : ι → ℕ) (src dst : E → ι)

/-- Descend every polynomial arrow and seed relation to a single coefficient ring. -/
theorem exists_diagram_coefficients
    (f : ∀ e, MvPolynomial (Fin (n (src e))) R →ₐ[R]
      MvPolynomial (Fin (n (dst e))) R)
    (s : ∀ i, Finset (MvPolynomial (Fin (n i)) R)) :
    ∃ S : Subring R, IsNoetherianRing S ∧
      (∀ i, (s i : Set (MvPolynomial (Fin (n i)) R)) ⊆
        Set.range (MvPolynomial.map S.subtype)) ∧
      ∃ f₀ : ∀ e, MvPolynomial (Fin (n (src e))) S →ₐ[S]
        MvPolynomial (Fin (n (dst e))) S,
        ∀ e, (f e).toRingHom.comp (MvPolynomial.map S.subtype) =
          (MvPolynomial.map S.subtype).comp (f₀ e).toRingHom := by
  classical
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite E
  let K := (Σ i, ↥(s i)) ⊕ (Σ e, Fin (n (src e)))
  let _ : Fintype K := inferInstanceAs (Fintype
    ((Σ i, ↥(s i)) ⊕ (Σ e, Fin (n (src e)))))
  let v : K → Type := fun k ↦ match k with
    | .inl ⟨i, _⟩ => Fin (n i)
    | .inr ⟨e, _⟩ => Fin (n (dst e))
  let p : ∀ k, MvPolynomial (v k) R := fun k ↦ match k with
    | .inl ⟨_, z⟩ => z.val
    | .inr ⟨e, z⟩ => f e (MvPolynomial.X z)
  obtain ⟨S, hS, h⟩ := exists_coefficient_ring p
  choose q hq using h
  let f₀ (e) : MvPolynomial (Fin (n (src e))) S →ₐ[S]
      MvPolynomial (Fin (n (dst e))) S :=
    MvPolynomial.aeval fun z ↦ q (.inr ⟨e, z⟩)
  refine ⟨S, hS, fun i z hz ↦ ⟨q (.inl ⟨i, ⟨z, hz⟩⟩), hq _⟩, f₀, fun e ↦ ?_⟩
  apply MvPolynomial.ringHom_ext
  · intro r
    change f e (MvPolynomial.map S.subtype (MvPolynomial.C r)) =
      MvPolynomial.map S.subtype
        (MvPolynomial.aeval (fun z ↦ q (.inr ⟨e, z⟩)) (MvPolynomial.C r))
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
    change f e (MvPolynomial.C (S.subtype r)) =
      MvPolynomial.map S.subtype (MvPolynomial.C r)
    rw [MvPolynomial.map_C]
    exact (f e).commutes (S.subtype r)
  · intro z
    change f e (MvPolynomial.map S.subtype (MvPolynomial.X z)) =
      MvPolynomial.map S.subtype
        (MvPolynomial.aeval (fun z ↦ q (.inr ⟨e, z⟩)) (MvPolynomial.X z))
    rw [MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact (hq (.inr ⟨e, z⟩)).symm

end FLT.Mazur.FinitePolynomialCoefficients
