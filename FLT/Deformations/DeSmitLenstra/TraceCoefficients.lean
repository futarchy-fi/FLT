/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.RepresentationTheory.Burnside
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Trace-pairing coefficient descent

An invertible Gram matrix over a coefficient ring lets us recover the coordinates of a vector
from its pairings.  Applied to the trace pairing and a Burnside basis, this descends all matrices
in a lifted representation to the trace-ring span of that basis.
-/

@[expose] public section

universe u

namespace Representation

noncomputable section

variable {S R M : Type u} [CommRing S] [CommRing R] [Algebra S R]
variable [AddCommGroup M] [Module R M]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Coordinates descend through a perfect pairing whose Gram matrix is already defined over the
smaller coefficient ring. -/
lemma repr_mem_algebraMap_range_of_pairing
    (b : Module.Basis ι R M) (B : LinearMap.BilinForm R M) (C : Matrix ι ι S)
    (hC : C.map (algebraMap S R) = B.toMatrix b) (hdet : IsUnit C.det)
    (x : M) (hx : ∀ j, B x (b j) ∈ Set.range (algebraMap S R)) :
    ∀ i, b.repr x i ∈ Set.range (algebraMap S R) := by
  choose p hp using hx
  have hCunit : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr hdet
  obtain ⟨a, ha⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hCunit) p
  have hmapC : IsUnit (C.map (algebraMap S R)) := hCunit.map (RingHom.mapMatrix _)
  have hrepr : Matrix.vecMul (fun i ↦ b.repr x i) (B.toMatrix b) =
      fun j ↦ B x (b j) := by
    ext j
    simp only [Matrix.vecMul, dotProduct, LinearMap.BilinForm.toMatrix_apply]
    let f : M →ₗ[R] R := LinearMap.flip B (b j)
    change (∑ i, b.repr x i * f (b i)) = f x
    have h := congrArg f (b.sum_repr x)
    rw [map_sum] at h
    simpa only [map_smul, smul_eq_mul] using h
  have ha' : (algebraMap S R) ∘ a = fun i ↦ b.repr x i := by
    apply Matrix.vecMul_injective_of_isUnit hmapC
    calc
      Matrix.vecMul ((algebraMap S R) ∘ a) (C.map (algebraMap S R)) =
          (algebraMap S R) ∘ p := by
        ext j
        rw [← RingHom.map_vecMul]
        change algebraMap S R (Matrix.vecMul a C j) = algebraMap S R (p j)
        have haj : Matrix.vecMul a C j = p j := congrFun ha j
        exact congrArg (algebraMap S R) haj
      _ = fun j ↦ B x (b j) := funext hp
      _ = Matrix.vecMul (fun i ↦ b.repr x i) (B.toMatrix b) := hrepr.symm
      _ = Matrix.vecMul (fun i ↦ b.repr x i) (C.map (algebraMap S R)) := by rw [hC]
  intro i
  exact ⟨a i, congrFun ha' i⟩

/-- A square matrix over a local ring is invertible when its determinant stays nonzero in the
residue field. -/
lemma isUnit_det_of_residue_det_ne_zero [IsLocalRing S] (C : Matrix ι ι S)
    (hC : (C.map (IsLocalRing.residue S)).det ≠ 0) : IsUnit C.det := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit C.det).mp
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  exact hC

omit [Fintype ι] [DecidableEq ι] in
/-- Coordinate descent places a vector in the span of the chosen basis over the smaller ring. -/
lemma mem_span_of_repr_mem_algebraMap_range [Finite ι]
    [Module S M] [IsScalarTower S R M]
    (b : Module.Basis ι R M) (x : M)
    (hx : ∀ i, b.repr x i ∈ Set.range (algebraMap S R)) :
    x ∈ Submodule.span S (Set.range b) := by
  classical
  let _ := Fintype.ofFinite ι
  rw [← b.sum_repr x]
  exact (Submodule.span S (Set.range b)).sum_mem fun i _ ↦ by
    obtain ⟨c, hc⟩ := hx i
    change b.repr x i • b i ∈ Submodule.span S (Set.range b)
    rw [← hc, algebraMap_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self i))

variable {G : Type u} {n : Type} [Group G] [Fintype n] [DecidableEq n]

/-- Matrix-valued monoid homomorphism attached to a representation on a coordinate space. -/
def representationMatrixHom (rho : Representation R G (n → R)) : G →* Matrix n n R :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp rho

@[simp]
lemma representationMatrixHom_apply (rho : Representation R G (n → R)) (g : G) :
    representationMatrixHom rho g = representationMatrix rho g := rfl

/-- The matrix algebra generated over `S` by the image of a representation over `R`. -/
def imageAlgebra (rho : Representation R G (n → R)) : Subalgebra S (Matrix n n R) :=
  Algebra.adjoin S (Set.range (representationMatrix rho))

/-- Trace-pairing descent for the matrices of a representation. -/
lemma repr_representationMatrix_mem_algebraMap_range
    (rho : Representation R G (n → R)) (g : ι → G)
    (b : Module.Basis ι R (Matrix n n R))
    (hb : ∀ i, b i = representationMatrix rho (g i))
    (C : Matrix ι ι S)
    (hC : C.map (algebraMap S R) =
      (fun i j ↦ (representationMatrix rho (g i * g j)).trace))
    (hdet : IsUnit C.det)
    (htrace : ∀ h, (representationMatrix rho h).trace ∈ Set.range (algebraMap S R))
    (h : G) : ∀ i, b.repr (representationMatrix rho h) i ∈
      Set.range (algebraMap S R) := by
  refine repr_mem_algebraMap_range_of_pairing b matrixTracePairing C ?_ hdet
    (representationMatrix rho h) ?_
  · rw [hC]
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, matrixTracePairing_apply, hb i, hb j]
    simp [representationMatrix]
  · intro j
    rw [matrixTracePairing_apply, hb j]
    simpa [representationMatrix] using htrace (h * g j)

/-- Every matrix in the representation lies in the trace-ring span of a lifted Burnside basis. -/
lemma representationMatrix_mem_span
    (rho : Representation R G (n → R)) (g : ι → G)
    (b : Module.Basis ι R (Matrix n n R))
    (hb : ∀ i, b i = representationMatrix rho (g i))
    (C : Matrix ι ι S)
    (hC : C.map (algebraMap S R) =
      (fun i j ↦ (representationMatrix rho (g i * g j)).trace))
    (hdet : IsUnit C.det)
    (htrace : ∀ h, (representationMatrix rho h).trace ∈ Set.range (algebraMap S R))
    (h : G) :
    representationMatrix rho h ∈ Submodule.span S (Set.range b) :=
  mem_span_of_repr_mem_algebraMap_range b _
    (repr_representationMatrix_mem_algebraMap_range rho g b hb C hC hdet htrace h)

omit [Fintype ι] [DecidableEq ι] in
/-- The image algebra is exactly the finite span of a lifted Burnside basis. -/
lemma imageAlgebra_toSubmodule_eq_span
    (rho : Representation R G (n → R)) (g : ι → G)
    (b : Module.Basis ι R (Matrix n n R))
    (hb : ∀ i, b i = representationMatrix rho (g i))
    (hall : ∀ h, representationMatrix rho h ∈ Submodule.span S (Set.range b)) :
    (imageAlgebra (S := S) rho).toSubmodule = Submodule.span S (Set.range b) := by
  have hadjoin : (imageAlgebra (S := S) rho).toSubmodule =
      Submodule.span S (Set.range (representationMatrix rho)) := by
    apply Algebra.adjoin_eq_span_of_subset
    change ↑(Submonoid.closure (Set.range (representationMatrixHom rho))) ⊆
      (Submodule.span S (Set.range (representationMatrix rho)) : Set (Matrix n n R))
    rw [MonoidHom.mclosure_range, MonoidHom.coe_mrange]
    exact Set.range_subset_iff.mpr fun h ↦ Submodule.subset_span ⟨h, rfl⟩
  rw [hadjoin]
  apply le_antisymm
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hall)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨g i, (hb i).symm⟩

/-- A lifted Burnside basis gives a finite free basis of the representation image algebra. -/
def imageAlgebraBasis [FaithfulSMul S R]
    (rho : Representation R G (n → R)) (g : ι → G)
    (b : Module.Basis ι R (Matrix n n R))
    (hb : ∀ i, b i = representationMatrix rho (g i))
    (hall : ∀ h, representationMatrix rho h ∈ Submodule.span S (Set.range b)) :
    Module.Basis ι S (imageAlgebra (S := S) rho) :=
  let hli : LinearIndependent S b := b.linearIndependent.restrict_scalars'
    S
  (Module.Basis.span hli).map
    (LinearEquiv.ofEq _ _ (imageAlgebra_toSubmodule_eq_span rho g b hb hall)).symm

/-- The finite free basis of the image algebra produced directly by trace-pairing descent. -/
def traceImageAlgebraBasis [FaithfulSMul S R]
    (rho : Representation R G (n → R)) (g : ι → G)
    (b : Module.Basis ι R (Matrix n n R))
    (hb : ∀ i, b i = representationMatrix rho (g i))
    (C : Matrix ι ι S)
    (hC : C.map (algebraMap S R) =
      (fun i j ↦ (representationMatrix rho (g i * g j)).trace))
    (hdet : IsUnit C.det)
    (htrace : ∀ h, (representationMatrix rho h).trace ∈ Set.range (algebraMap S R)) :
    Module.Basis ι S (imageAlgebra (S := S) rho) :=
  imageAlgebraBasis rho g b hb fun h ↦
    representationMatrix_mem_span rho g b hb C hC hdet htrace h

end

end Representation
