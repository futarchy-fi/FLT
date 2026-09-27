/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep

/-!
# Flat prolongations and coefficient quotients

A finite-flat model of a representation gives finite-flat models of all its
coefficient quotients. This supplies the open-ideal condition in `IsFlatAt`.
-/

@[expose] public section

open NumberField
open scoped TensorProduct

universe u

namespace GaloisRep

variable {K M : Type u} {A : Type} [Field K] [NumberField K]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : GaloisRep K A M)

/-- A finite-flat prolongation remains finite flat after quotienting the coefficient ring. -/
theorem HasFlatProlongationAt.quotient (hρ : ρ.HasFlatProlongationAt v) (I : Ideal A) :
    (ρ.baseChange (A ⧸ I)).HasFlatProlongationAt v := by
  let q : (ρ.toLocal v).Space →+[Field.absoluteGaloisGroup (v.adicCompletion K)]
      ((ρ.baseChange (A ⧸ I)).toLocal v).Space :=
    { (TensorProduct.mk A (A ⧸ I) M 1).toAddMonoidHom with
      map_smul' := fun _ _ ↦ rfl }
  exact GaloisModule.IsFiniteFlat.quotient _ _ _ _ hρ q
    (TensorProduct.mk_surjective (R := A) (S := A ⧸ I) (M := M) Ideal.Quotient.mk_surjective)

/-- A finite-flat prolongation implies flatness at the place, including all open
coefficient ideals required by `IsFlatAt`. -/
theorem HasFlatProlongationAt.isFlatAt [IsLocalRing A]
    (hρ : ρ.HasFlatProlongationAt v) : ρ.IsFlatAt v := by
  exact ⟨fun I _ ↦ hρ.quotient v ρ I⟩

end GaloisRep
