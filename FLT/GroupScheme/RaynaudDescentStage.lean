/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.InertiaDescentUniformizer
public import FLT.GroupScheme.RaynaudStageFamily

/-!
# The actual inertia descent integers in the original unramified union

Preservation of the original uniformizer and separability of the finite
residue field place the prescribed embedded descent ring in the stage family.
-/

@[expose] public noncomputable section

open NumberField IsLocalRing IsDiscreteValuationRing
namespace RaynaudParameters

variable {F X : Type} [Field F] [NumberField F]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) [AddCommGroup X]
  [DistribMulAction (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F]
    AlgebraicClosure (v.adicCompletion F)) X]
  [Finite X] [ContinuousSMulDiscrete (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F]
    AlgebraicClosure (v.adicCompletion F)) X]

local notation "R" => v.adicCompletionIntegers F
local notation "Ωv" => AlgebraicClosure (v.adicCompletion F)
local notation "L" => InertiaDescent.field (X := X) (localInertiaGroup v)
local notation "S" => IntegralClosure R L

/-- The actual finite descent integers are formally unramified. -/
theorem inertiaDescentIntegers_unramified : Algebra.FormallyUnramified R S := by
  let : Module.Finite R S := IsIntegralClosure.finite R (v.adicCompletion F) L S
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπS := inertiaDescentIntegers_irreducible (X := X) v hπ
  apply Algebra.FormallyUnramified.of_map_maximalIdeal
  rw [hπ.maximalIdeal_eq, hπS.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

/-- The descent integers retain their prescribed embedding in the original closure. -/
def inertiaDescentIntegersEmbedding : S →ₐ[R] Ωv :=
  (IsScalarTower.toAlgHom R L Ωv).comp (IsScalarTower.toAlgHom R S L)

/-- The image of the actual descent integers is an unramified stage. -/
def inertiaDescentStage {π : R} (hπ : Irreducible π) : UnramifiedStage (Ω := Ωv) π := by
  let f := inertiaDescentIntegersEmbedding (X := X) v
  have hf : Function.Injective f :=
    (FaithfulSMul.algebraMap_injective L Ωv).comp (IsFractionRing.injective S L)
  let e : S ≃ₐ[R] f.range := AlgEquiv.ofInjective f hf
  let : Module.Finite R S := IsIntegralClosure.finite R (v.adicCompletion F) L S
  let : Algebra.FormallyUnramified R S := inertiaDescentIntegers_unramified (X := X) v
  let hD := RingEquivClass.isDiscreteValuationRing e
  let hF : Module.Finite R f.range := Module.Finite.of_surjective e.toLinearMap e.surjective
  let hU : Algebra.FormallyUnramified R f.range := Algebra.FormallyUnramified.of_equiv e
  refine ⟨f.range, hD, hF, hU, ?_⟩
  have h := (inertiaDescentIntegers_irreducible (X := X) v hπ).map e.toMulEquiv
  change Irreducible (e (algebraMap R S π)) at h
  simpa only [e.commutes] using h

/-- Every actual descent integer lies in the original unramified union. -/
theorem inertiaDescentIntegers_mem_union {π : R} (hπ : Irreducible π) (x : S) :
    inertiaDescentIntegersEmbedding (X := X) v x ∈ unramifiedUnion (Ω := Ωv) π := by
  apply (le_iSup (fun T : UnramifiedStage (Ω := Ωv) π ↦ T.1)
    (inertiaDescentStage (X := X) v hπ))
  exact ⟨x, rfl⟩

/-- The prescribed embedding factors through the original union. -/
def inertiaDescentIntegersToUnion {π : R} (hπ : Irreducible π) :
    S →ₐ[R] unramifiedUnion (Ω := Ωv) π :=
  (inertiaDescentIntegersEmbedding (X := X) v).codRestrict _
    (inertiaDescentIntegers_mem_union (X := X) v hπ)

end RaynaudParameters
