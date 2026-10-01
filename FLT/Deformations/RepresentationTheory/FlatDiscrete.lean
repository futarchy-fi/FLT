/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.Flat

/-!
# Flatness over discrete coefficient rings

The zero ideal is open for discrete coefficients, so flatness of all open
reductions is equivalent to a finite-flat model of the representation itself.
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

/-- Over discrete coefficients, the zero-ideal reduction recovers a flat model
of the original representation. Conversely, quotient closure supplies all reductions. -/
theorem isFlatAt_iff_hasFlatProlongationAt [IsLocalRing A] [DiscreteTopology A] :
    ρ.IsFlatAt v ↔ ρ.HasFlatProlongationAt v := by
  constructor
  · intro hρ
    let e : (A ⧸ (⊥ : Ideal A)) ⊗[A] M ≃ₗ[A] M :=
      (TensorProduct.congr (AlgEquiv.quotientBot A A).toLinearEquiv
        (LinearEquiv.refl A M)).trans (TensorProduct.lid A M)
    let q : ((ρ.baseChange (A ⧸ (⊥ : Ideal A))).toLocal v).Space →+[
        Field.absoluteGaloisGroup (v.adicCompletion K)] (ρ.toLocal v).Space :=
      { e.toAddMonoidHom with
        map_smul' := by
          intro σ x
          change e (((ρ.baseChange (A ⧸ (⊥ : Ideal A))).toLocal v) σ x) =
            (ρ.toLocal v) σ (e x)
          induction x using TensorProduct.inductionOn with
          | tmul a x => simp [e, baseChange_map, baseChange_tmul]
          | add x y hx hy => simp_all }
    exact (hρ.cond ⊥ (isOpen_discrete _)).map _ _ _ _ q e.bijective
  · exact fun hρ ↦ hρ.isFlatAt v ρ

end GaloisRep
