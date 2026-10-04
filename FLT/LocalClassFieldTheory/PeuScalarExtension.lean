/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PeuCoefficientTransport
public import FLT.GaloisRepresentation.Extensions.TensorCharacterClasses

/-!
# Scalar extension of the independent cup condition

Decompose the unramified dual character in a finite coefficient basis and
extend each actual bounding cochain. This proves the forward implication
without assuming compatibility of the arithmetic pairing.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open GaloisRepresentation.Extensions

variable {G F k ι : Type*} [Group G] [TopologicalSpace G]
  [Field F] [TopologicalSpace F] [DiscreteTopology F]
  [Field k] [TopologicalSpace k] [DiscreteTopology k] [Algebra F k]
  [Finite ι] (χ : G →* Fˣ) (b : Module.Basis ι F k)

/-- A coordinate of a continuous scalar character is a continuous scalar character. -/
def scalarCharacterCoordinate (d : ContinuousAddCharacter G k) (i : ι) :
    ContinuousAddCharacter G F :=
  ⟨⟨fun g => b.repr (d.1 g) i, (continuous_of_discreteTopology
      (f := fun a : k => b.repr a i)).comp d.1.continuous⟩,
    fun g h => by simp only [ContinuousMap.coe_mk, d.2, map_add, Finsupp.add_apply]⟩

omit [DiscreteTopology F] [Finite ι] in
/-- Coordinate characters remain trivial on inertia. -/
theorem scalarCharacterCoordinate_unramified (I : Subgroup G)
    (d : ContinuousAddCharacter G k) (hd : IsUnramifiedAddCharacter I d) (i : ι) :
    IsUnramifiedAddCharacter I (scalarCharacterCoordinate b d i) := by
  intro g hg
  change b.repr (d.1 g) i = 0
  rw [hd g hg, map_zero, Finsupp.zero_apply]

/-- Include a scalar character through the actual field embedding. -/
def scalarCharacterInclusion (d : ContinuousAddCharacter G F) :
    ContinuousAddCharacter G k :=
  ⟨⟨fun g => algebraMap F k (d.1 g), (continuous_of_discreteTopology
      (f := algebraMap F k)).comp d.1.continuous⟩,
    fun g h => by simp only [ContinuousMap.coe_mk, d.2, map_add]⟩

omit [DiscreteTopology k] in
/-- Inclusion preserves the independent inertia-trivial condition. -/
theorem scalarCharacterInclusion_unramified (I : Subgroup G)
    (d : ContinuousAddCharacter G F) (hd : IsUnramifiedAddCharacter I d) :
    IsUnramifiedAddCharacter I (scalarCharacterInclusion (k := k) d) := by
  intro g hg
  change algebraMap F k (d.1 g) = 0
  rw [hd g hg, map_zero]

include b in
/-- Coefficient inclusion preserves peu-ramification, including every extended dual character. -/
theorem peuCocycle_inclusion (I : Subgroup G)
    (c : linearContinuousCocycles F G (CharacterModule χ F))
    (hc : c ∈ peuCocycleSubmodule I) :
    linearCocycleMap (characterInclusionSemilinear (k := k) χ)
      (characterCoefficientInclusion_equivariant χ k) c ∈ peuCocycleSubmodule I := by
  intro d hd
  classical
  let := Fintype.ofFinite ι
  let z (i : ι) : C(G × G, CharacterModule χ k) :=
    ⟨fun gh => algebraMap F k (continuousCup (linearCocycleForget c)
        (scalarCharacterCoordinate b d i) gh),
      (continuous_of_discreteTopology (f := characterCoefficientInclusion χ k)).comp
        (continuousCup (linearCocycleForget c) (scalarCharacterCoordinate b d i)).continuous⟩
  have hz (i : ι) : ContinuousIsCoboundaryTwo (z i) :=
    continuousBoundary_map (characterCoefficientInclusion χ k)
      (characterCoefficientInclusion_equivariant χ k) _
      (hc _ (scalarCharacterCoordinate_unramified b I d hd i))
  have hs := continuousBoundary_sum Finset.univ (fun i => b i • z i)
    (fun i _ => continuousBoundary_smul (b i) (z i) (hz i))
  convert hs using 1
  apply ContinuousMap.ext
  intro gh
  change d.1 gh.2 * algebraMap F k (c.1 gh.1) =
    (∑ i, b i • z i) gh
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  change _ = ∑ i, b i * algebraMap F k (b.repr (d.1 gh.2) i * (show F from c.1 gh.1))
  have hm (a : k) (v : F) :
      a * algebraMap F k v = ∑ i, b i * algebraMap F k (b.repr a i * v) := by
    simp only [map_mul, ← mul_assoc, ← Finset.sum_mul]
    congr 1
    simpa only [Algebra.smul_def, mul_comm] using (b.sum_repr a).symm
  exact hm _ _

end LocalClassFieldTheory
