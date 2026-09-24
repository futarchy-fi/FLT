/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.CompletionComparison

/-!
# The finite local compositum

Identify a finite global subextension after adjoining the completed base field,
and identify its fixing subgroup with the kernel of local restriction.
-/

@[expose] public section

open NumberField IsDedekindDomain.HeightOneSpectrum
namespace NumberField.InertiaComparison
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
variable (L : IntermediateField K (AlgebraicClosure K))
local notation "Kv" => v.adicCompletion K

/-- The chosen embedding of the global subextension into the local algebraic closure. -/
noncomputable def localEmbedding : L →ₐ[K] AlgebraicClosure Kv where
  __ := (AlgebraicClosure.map (algebraMap K Kv)).comp L.val.toRingHom
  commutes' := fun x ↦ AlgebraicClosure.map_algebraMap _ x

/-- The compositum of the global subextension and the completed base field. -/
noncomputable def localCompositum : IntermediateField Kv (AlgebraicClosure Kv) :=
  IntermediateField.adjoin Kv (Set.range (localEmbedding v L))

/-- A completion realizing the chosen embedding is isomorphic to the local compositum. -/
noncomputable def completionEquivLocalCompositum [FiniteDimensional K L]
    (w : v.Extension (𝓞 L)) (g : w.1.adicCompletion L →ₐ[Kv] AlgebraicClosure Kv)
    (hg : ∀ x : L, g (algebraMap L _ x) = localEmbedding v L x) :
    w.1.adicCompletion L ≃ₐ[Kv] localCompositum v L :=
  g.equivFieldRange.trans (IntermediateField.equivOfEq
    (NumberField.fieldRange_eq_adjoin_of_completion_embedding v (localEmbedding v L) w g hg))

/-- The local compositum of a finite global extension is finite. -/
instance localCompositum_finiteDimensional [FiniteDimensional K L] :
    FiniteDimensional Kv (localCompositum v L) := by
  obtain ⟨w, g, _, hg⟩ := exists_inducedPrime_completion_embedding v L
  exact Module.Finite.equiv (completionEquivLocalCompositum v L w g hg).toLinearEquiv

variable [Normal K L]

/-- The chosen field embedding intertwines local restriction with the local action. -/
lemma localEmbedding_equivariant (σ : Field.absoluteGaloisGroup Kv) (x : L) :
    localEmbedding v L (localRestriction v L σ x) = σ (localEmbedding v L x) := by
  exact (congrArg (AlgebraicClosure.map (algebraMap K Kv))
    (AlgEquiv.restrictNormalHom_apply L
      (Field.absoluteGaloisGroup.map (algebraMap K Kv) σ) x)).trans
        (Field.absoluteGaloisGroup.lift_map _ _ _)

/-- A local automorphism fixes the compositum exactly when its global restriction is trivial. -/
lemma localCompositum_fixingSubgroup :
    (localCompositum v L).fixingSubgroup = (localRestriction v L).ker := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_ker]
  constructor
  · intro h
    apply AlgEquiv.ext
    intro x
    apply (localEmbedding v L).injective
    change localEmbedding v L (localRestriction v L σ x) = localEmbedding v L x
    rw [localEmbedding_equivariant]
    exact h _ (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  · intro h x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      rw [← localEmbedding_equivariant, h]
      rfl
    | algebraMap x => exact σ.commutes x
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | inv x _ hx => simp only [map_inv₀, hx]
    | mul x y _ _ hx hy => simp only [map_mul, hx, hy]

/-- The local compositum of a normal global extension is Galois over the completion. -/
instance localCompositum_isGalois : IsGalois Kv (localCompositum v L) := by
  rw [← InfiniteGalois.normal_iff_isGalois, localCompositum_fixingSubgroup]
  infer_instance

end NumberField.InertiaComparison
