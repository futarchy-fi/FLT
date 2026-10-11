/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCoordinateSlice
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.Data.Fin.VecNotation

/-!
# Étale coefficient algebras for finite simple-root coordinates

Adjoin each monic root and invert the derivative. Iterating this construction
lifts a finite tuple of simple roots into one actual étale coefficient algebra.
The field-valued evaluation and its original base map are retained exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
namespace FLT.Mazur.EtaleSimpleRootCoordinates
variable {R K : Type} [CommRing R] [Field K]

/-- A simple root lifts into its derivative-localized standard étale algebra. -/
theorem exists_root (φ : R →+* K) (p : R[X]) (hp : p.Monic) (v : K)
    (hv : p.eval₂ φ v = 0) (hd : p.derivative.eval₂ φ v ≠ 0) :
    ∃ (A : CommRingCat.{0}) (a : R →+* A) (q : A →+* K) (x : A),
      a.Etale ∧ q.comp a = φ ∧ q x = v := by
  let P : StandardEtalePair R := ⟨p, hp, p.derivative, 1, 0, 1, by simp⟩
  let _ := φ.toAlgebra
  have h : P.HasMap v := ⟨hv, isUnit_iff_ne_zero.mpr hd⟩
  let q := P.lift v h
  refine ⟨.of P.Ring, algebraMap R P.Ring, q.toRingHom, P.X, ?_, ?_, ?_⟩
  · exact RingHom.etale_algebraMap.mpr inferInstance
  · ext r
    exact q.commutes r
  · exact P.lift_X v h

/-- Finite simple-root coordinates lift together into an étale algebra over the original ring. -/
theorem exists_family (φ : R →+* K) {n : ℕ} (p : Fin n → R[X])
    (hp : ∀ i, (p i).Monic) (v : Fin n → K)
    (hv : ∀ i, (p i).eval₂ φ (v i) = 0)
    (hd : ∀ i, (p i).derivative.eval₂ φ (v i) ≠ 0) :
    ∃ (A : CommRingCat.{0}) (a : R →+* A) (q : A →+* K) (x : Fin n → A),
      a.Etale ∧ q.comp a = φ ∧ ∀ i, q (x i) = v i := by
  induction n generalizing R with
  | zero =>
    exact ⟨.of R, RingHom.id R, φ, Fin.elim0,
      RingHom.Etale.containsIdentities R, rfl, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨A, a, q, x, ha, hq, hx⟩ := exists_root φ (p 0) (hp 0) (v 0) (hv 0) (hd 0)
    have hv' (i : Fin n) : ((p i.succ).map a).eval₂ q (v i.succ) = 0 := by
      rw [eval₂_map, hq]
      exact hv i.succ
    have hd' (i : Fin n) : ((p i.succ).map a).derivative.eval₂ q (v i.succ) ≠ 0 := by
      rw [derivative_map, eval₂_map, hq]
      exact hd i.succ
    obtain ⟨B, b, t, y, hb, ht, hy⟩ := ih q (fun i ↦ (p i.succ).map a)
      (fun i ↦ (hp i.succ).map a) (fun i ↦ v i.succ) hv' hd'
    refine ⟨B, b.comp a, t, Fin.cons (b x) y,
      RingHom.Etale.stableUnderComposition a b ha hb, ?_, ?_⟩
    · rw [← RingHom.comp_assoc, ht, hq]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact (RingHom.congr_fun ht x).trans hx
      · exact hy j

end FLT.Mazur.EtaleSimpleRootCoordinates
