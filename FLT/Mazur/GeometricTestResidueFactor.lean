/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothGeometricOpenEtaleLift
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Original residue factorization of an arbitrary geometric test

The kernel of the original coefficient map constructs a residue field and
its preimmersion into the unchanged affine base. The whole geometric base
map is recovered by scalar extension, without any algebraicity hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeometricTestResidueFactor
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K]

/-- Every field-valued original test factors through a constructed residue preimmersion. -/
theorem exists_factor (q : Spec (.of K) ⟶ Spec (.of R)) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra k K) (t : Spec (.of k) ⟶ Spec (.of R)),
      IsPreimmersion t ∧ Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t = q := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective q
  let p := RingHom.ker ψ.hom
  let _ : p.IsPrime := RingHom.ker_isPrime ψ.hom
  have hu : p.primeCompl ≤ (IsUnit.submonoid K).comap ψ.hom := by
    intro r hr
    change IsUnit (ψ.hom r)
    exact isUnit_iff_ne_zero.mpr hr
  let θ := Ideal.ResidueField.lift p ψ.hom le_rfl hu
  let _ := θ.toAlgebra
  let t := Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))
  have ht : IsPreimmersion t := IsPreimmersion.mk_SpecMap
    (Topology.IsEmbedding.of_subsingleton _) p.surjectiveOnStalks_residueField
  refine ⟨p.ResidueField, inferInstance, inferInstance, t, ht, ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact Ideal.ResidueField.lift_algebraMap p ψ.hom le_rfl hu r

end FLT.Mazur.GeometricTestResidueFactor
