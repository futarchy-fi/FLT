/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteCharacterInertia
public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationClass

/-!
# The ordinary absolute action on a constructed finite DVR model

Continuity of the middle representation supplies continuity of its line ratio.
Its actual finite Galois fixed field then discharges the wild action equation.
The specified niveau-one character and the symmetric-power factors remain separate.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions.OrdinaryFiltration
variable {G k V : Type*} [Group G] [TopologicalSpace G]
  [Field k] [TopologicalSpace k] [DiscreteTopology k]
  [AddCommGroup V] [Module k V] [TopologicalSpace V] [DiscreteTopology V]
  {ρ : Representation k G V} {α β : G →* kˣ} (E : OrdinaryFiltration ρ α β)
  (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x))

include E hρ
omit [DiscreteTopology k] in
/-- Continuity of the injected-line character follows from the original orbit maps. -/
theorem continuous_subCharacter : Continuous (fun g : G ↦ (α g : k)) := by
  have h := (continuous_of_discreteTopology :
    Continuous (Function.invFun E.injection)).comp (hρ (E.injection 1))
  have hinv (a : k) : Function.invFun E.injection (E.injection a) = a :=
    Function.leftInverse_invFun E.injective a
  simpa only [Function.comp_def, E.injection_equivariant, mul_one, hinv] using h

include E hρ in
/-- Both coordinates of the unit-valued ratio are continuous. -/
theorem continuous_ratioCharacter : Continuous (α / β) := by
  have h (f : k × k → k) : Continuous (fun g : G ↦ f ((α g : k), (β g : k))) :=
    (continuous_of_discreteTopology (f := f)).comp
      ((E.continuous_subCharacter hρ).prodMk (E.continuous_quotientCharacter hρ))
  rw [Units.continuous_iff]
  constructor
  · simpa only [Function.comp_def, MonoidHom.div_apply, Units.val_div_eq_div_val]
      using h (fun t ↦ t.1 / t.2)
  · simpa using h (fun t ↦ (t.1 / t.2)⁻¹)

end GaloisRepresentation.Extensions.OrdinaryFiltration

open NumberField IsLocalRing LocalRamification
namespace GaloisRepresentation.Extensions
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  {k V : Type*} [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
  [AddCommGroup V] [Module k V] [TopologicalSpace V] [DiscreteTopology V]
  {ρ : Representation k (Field.absoluteGaloisGroup (v.adicCompletion K)) V}
  {α β : Field.absoluteGaloisGroup (v.adicCompletion K) →* kˣ}
  (E : OrdinaryFiltration ρ α β)
  (hρ : ∀ x : V, Continuous (fun g ↦ ρ g x))

/-- The finite Galois field is chosen from the actual ordinary line ratio. -/
def ordinaryRatioFiniteKernel :
    OpenNormalSubgroup (Field.absoluteGaloisGroup (v.adicCompletion K)) :=
  characterOpenNormal v (α / β) (E.continuous_ratioCharacter hρ)

attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR

set_option synthInstance.maxHeartbeats 100000 in
-- Synthesizing the constructed finite integral-closure action needs a larger budget.
set_option maxHeartbeats 1000000 in
-- The DVR instance in the dependent uniformizer type requires additional elaboration time.
/-- The original absolute ordinary action satisfies the wild equation on its constructed DVR. -/
theorem ordinary_absolute_finiteDVR_action (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField (v.adicCompletionIntegers K)) p] [CharP k p]
    {π : IntegralClosure (v.adicCompletionIntegers K)
      (IntermediateField.fixedField (ordinaryRatioFiniteKernel v E hρ).toSubgroup)}
    (hπ : Irreducible π) (g : localInertiaGroup v)
    (hg : ThreeAdicPlan.uniformizerCharacter hπ
      (finiteIdealInertiaRestriction v (ordinaryRatioFiniteKernel v E hρ) g) = 1) :
    ρ g.val (E.injection 1) = (β g.val : k) • E.injection 1 := by
  have h := finiteModelCharacter_uniformizer_kernel v (α / β)
    (E.continuous_ratioCharacter hρ) p hπ g hg
  change α g.val / β g.val = 1 at h
  have he := div_eq_one.mp h
  rw [E.injection_equivariant, mul_one, he, ← map_smul, smul_eq_mul, mul_one]

end GaloisRepresentation.Extensions
