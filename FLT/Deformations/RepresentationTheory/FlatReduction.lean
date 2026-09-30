/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.Flat
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Finite-flat models along coefficient reductions

For ideals `I ≤ J`, the equivariant surjection from the reduction modulo `I`
to the reduction modulo `J` carries finite flatness to the latter.
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

/-- A model modulo a smaller coefficient ideal supplies a model modulo any
larger ideal. No openness assumption on either ideal is needed. -/
theorem hasFlatProlongationAt_quotient_of_le {I J : Ideal A} (hIJ : I ≤ J)
    (hI : (ρ.baseChange (A ⧸ I)).HasFlatProlongationAt v) :
    (ρ.baseChange (A ⧸ J)).HasFlatProlongationAt v := by
  let f := (Ideal.Quotient.factorₐ A hIJ).toLinearMap
  let t := TensorProduct.map f (LinearMap.id : M →ₗ[A] M)
  let q : ((ρ.baseChange (A ⧸ I)).toLocal v).Space →+[
      Field.absoluteGaloisGroup (v.adicCompletion K)]
      ((ρ.baseChange (A ⧸ J)).toLocal v).Space :=
    { t.toAddMonoidHom with
      map_smul' := by
        intro σ x
        change t (((ρ.baseChange (A ⧸ I)).toLocal v) σ x) =
          ((ρ.baseChange (A ⧸ J)).toLocal v) σ (t x)
        induction x using TensorProduct.inductionOn with
        | tmul a x => simp [t, baseChange_map, baseChange_tmul]
        | add x y hx hy => simp_all }
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have ht : Function.Surjective t :=
    TensorProduct.map_surjective hf Function.surjective_id
  exact GaloisModule.IsFiniteFlat.quotient _ _ _ _ hI q ht

end GaloisRep
