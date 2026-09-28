/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.InvariantDerivation
public import FLT.Mathlib.RingTheory.AugmentationCotangent
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Coordinate derivations of local commutative bialgebras

Lifts of a cotangent basis admit derivations taking Kronecker-delta values on
those lifts. Extend the dual cotangent basis invariantly, then invert its
coordinate matrix: the matrix reduces to the identity under the counit, so
its determinant is a unit in the local algebra.
-/

@[expose] public noncomputable section

namespace Bialgebra

variable {k A ι : Type*} [Field k] [CommRing A] [Bialgebra k A]
  [IsLocalRing A] [Finite ι] [DecidableEq ι]

/-- Every lifted cotangent basis of a local bialgebra has coordinate derivations. -/
theorem exists_coordinate_derivations
    (b : Module.Basis ι k (RingHom.ker (counitAlgHom k A)).Cotangent)
    (x : ι → RingHom.ker (counitAlgHom k A))
    (hx : ∀ i, (RingHom.ker (counitAlgHom k A)).toCotangent (x i) = b i) :
    ∃ D : ι → Derivation k A A, ∀ i j, D i (x j) = if i = j then 1 else 0 := by
  let := Fintype.ofFinite ι
  let ε := counitAlgHom k A
  let d (i : ι) : A →ₗ[k] k := (b.coord i).comp ε.augmentationCotangent
  have h1 (i : ι) : d i 1 = 0 := by simp [d]
  have hd (i : ι) (a c : A) :
      d i (a * c) = Coalgebra.counit (R := k) a * d i c +
        Coalgebra.counit (R := k) c * d i a := by
    simp only [d, LinearMap.comp_apply, ε.augmentationCotangent_mul,
      map_add, map_smul, smul_eq_mul]
    rfl
  let E (i : ι) : Derivation k A A := invariantDerivation (d i) (h1 i) (hd i)
  have hE (i j : ι) : ε (E i (x j)) = if i = j then 1 else 0 := by
    change Coalgebra.counit (R := k) (invariantDerivation (d i) (h1 i) (hd i) (x j)) = _
    rw [counit_invariantDerivation]
    change b.coord i (ε.augmentationCotangent (x j)) = _
    rw [ε.augmentationCotangent_of_mem, hx]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply, eq_comm]
  let M : Matrix ι ι A := fun i j ↦ E i (x j)
  have hM : M.map ε = 1 := by
    ext i j
    exact hE i j
  let : IsLocalHom ε.toRingHom := IsLocalHom.of_surjective _
    (fun c ↦ ⟨algebraMap k A c, ε.commutes c⟩)
  have hdet : IsUnit M.det := by
    apply isUnit_of_map_unit ε.toRingHom
    change IsUnit (ε M.det)
    rw [ε.map_det]
    change IsUnit (M.map ε).det
    rw [hM, Matrix.det_one]
    exact isUnit_one
  refine ⟨fun i ↦ ∑ l, M⁻¹ i l • E l, fun i j ↦ ?_⟩
  have h := congrArg (fun N : Matrix ι ι A ↦ N i j) (Matrix.nonsing_inv_mul M hdet)
  change (Derivation.coeAddMonoidHom (∑ l, M⁻¹ i l • E l)) (x j) = _
  rw [map_sum, LinearMap.sum_apply]
  change (∑ l, M⁻¹ i l * E l (x j)) = _
  simpa only [Matrix.mul_apply, Matrix.one_apply] using h

end Bialgebra
