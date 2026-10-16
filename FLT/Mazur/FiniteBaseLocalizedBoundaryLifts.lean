/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteBaseLocalizationDenominators

/-!
# Exact boundary lifts from localization at original scalars

Compatible localized solutions on finitely many charts construct exact original
numerators. Their boundary is multiplied by one scalar in the prescribed
multiplicative set, so a prime complement retains nonvanishing at that prime.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteBaseLocalizedBoundaryLifts
open FiniteBaseLocalizationDenominators
variable {R : Type*} [CommRing R] (M : Submonoid R)
  {ι : Type*} [Finite ι] {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  (α : ∀ i, R →+* A i)
  (φ : ∀ i, A i →+* B i) (p : ∀ i j, A i →+* C i j) (q : ∀ i j, A j →+* C i j)
  (hα : ∀ i j x, p i j (α i x) = q i j (α j x))
  {S T : ι → Type*} {U : ι → ι → Type*}
  [∀ i, CommRing (S i)] [∀ i, CommRing (T i)] [∀ i j, CommRing (U i j)]
  [∀ i, Algebra (A i) (S i)] [∀ i, Algebra (B i) (T i)]
  [∀ i j, Algebra (C i j) (U i j)]
  [∀ i, IsLocalization (M.map (α i).toMonoidHom) (S i)]
  [∀ i, IsLocalization (M.map ((φ i).comp (α i)).toMonoidHom) (T i)]
  [∀ i j, IsLocalization (M.map ((p i j).comp (α i)).toMonoidHom) (U i j)]
  (β : ∀ i, S i →+* T i) (π : ∀ i j, S i →+* U i j) (ρ : ∀ i j, S j →+* U i j)
  (hβ : ∀ i x, β i (algebraMap _ _ x) = algebraMap _ _ (φ i x))
  (hπ : ∀ i j x, π i j (algebraMap _ _ x) = algebraMap _ _ (p i j x))
  (hρ : ∀ i j x, ρ i j (algebraMap _ _ x) = algebraMap _ _ (q i j x))

include hα hβ hπ hρ

/-- One allowed original scalar clears the fractions and every boundary and full mixed error. -/
theorem exists_exact_numerators (v : ∀ i, S i) (t : ∀ i, B i)
    (hb : ∀ i, β i (v i) = algebraMap _ _ (t i))
    (he : ∀ i j, π i j (v i) = ρ i j (v j)) :
    ∃ s : M, ∃ w : ∀ i, A i,
      (∀ i, φ i (w i) = φ i (α i s) * t i) ∧
      (∀ i j, p i j (w i) = q i j (w j)) := by
  obtain ⟨s, a, ha⟩ := exists_numerators M α v
  have hb' (i : ι) : algebraMap (B i) (T i) (φ i (a i)) =
      algebraMap (B i) (T i) (φ i (α i s) * t i) := by
    rw [← hβ i, ha i, map_mul, hβ, hb i, map_mul]
  obtain ⟨b, hb''⟩ := exists_equalities M (fun i ↦ (φ i).comp (α i))
    (fun i ↦ φ i (a i)) (fun i ↦ φ i (α i s) * t i) hb'
  have he' (ij : ι × ι) :
      algebraMap (C ij.1 ij.2) (U ij.1 ij.2) (p ij.1 ij.2 (a ij.1)) =
      algebraMap (C ij.1 ij.2) (U ij.1 ij.2) (q ij.1 ij.2 (a ij.2)) := by
    rw [← hπ ij.1 ij.2, ← hρ ij.1 ij.2, ha ij.1, ha ij.2]
    simp only [map_mul, hπ, hρ, ← hα, he ij.1 ij.2]
  obtain ⟨c, hc⟩ := exists_equalities M (fun ij : ι × ι ↦ (p ij.1 ij.2).comp (α ij.1))
    (fun ij ↦ p ij.1 ij.2 (a ij.1)) (fun ij ↦ q ij.1 ij.2 (a ij.2)) he'
  refine ⟨c * b * s, fun i ↦ α i c * α i b * a i, ?_, ?_⟩
  · intro i
    have hi := hb'' i
    simp only [RingHom.comp_apply] at hi
    simp only [Submonoid.coe_mul, map_mul]
    rw [mul_assoc, hi]
    ring
  · intro i j
    have hij := hc (i, j)
    simp only [RingHom.comp_apply] at hij
    simp only [map_mul, ← hα]
    calc
      _ = p i j (α i b) * (p i j (α i c) * p i j (a i)) := by ring
      _ = p i j (α i b) * (p i j (α i c) * q i j (a j)) := by rw [hij]
      _ = _ := by ring

end FLT.Mazur.FiniteBaseLocalizedBoundaryLifts
