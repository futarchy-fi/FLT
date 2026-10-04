/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PeuScalarExtension

/-!
# Detecting the extended cup annihilator in prime coordinates

Prime-valued test characters recover each coordinate of an extended class.
Conversely, coefficient inclusion and finite reconstruction prove that all
prime coordinates suffice, even against extended-valued test characters.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open GaloisRepresentation.Extensions

variable {G F k ι : Type*} [Group G] [TopologicalSpace G]
  [Field F] [TopologicalSpace F] [DiscreteTopology F]
  [Field k] [TopologicalSpace k] [DiscreteTopology k] [Algebra F k]
  [Fintype ι] (χ : G →* Fˣ) (b : Module.Basis ι F k)

/-- A coefficient coordinate detects peu-ramification using included prime dual characters. -/
theorem peuCocycle_coordinate (I : Subgroup G)
    (c : linearContinuousCocycles k G (CharacterModule χ k))
    (hc : c ∈ peuCocycleSubmodule I) (i : ι) :
    linearCocycleMap (characterCoordinateMap χ b i)
      (characterCoordinateMap_equivariant χ b i) (linearCocycleOf (linearCocycleForget c)) ∈
        peuCocycleSubmodule I := by
  intro d hd
  have hz := hc (scalarCharacterInclusion (k := k) d)
    (scalarCharacterInclusion_unramified I d hd)
  have h := continuousBoundary_map (characterCoordinateMap χ b i)
    (characterCoordinateMap_equivariant χ b i) _ hz
  convert h using 1
  apply ContinuousMap.ext
  intro gh
  change d.1 gh.2 * b.repr (c.1 gh.1) i =
    b.repr (algebraMap F k (d.1 gh.2) * (show k from c.1 gh.1)) i
  rw [← Algebra.smul_def, map_smul]
  rfl

/-- The extended cocycle predicate is equivalent to the independent prime-coordinate predicates. -/
theorem peuCocycle_coordinates_iff (I : Subgroup G)
    (c : linearContinuousCocycles k G (CharacterModule χ k)) :
    c ∈ peuCocycleSubmodule I ↔
      ∀ i, linearCocycleMap (characterCoordinateMap χ b i)
        (characterCoordinateMap_equivariant χ b i)
        (linearCocycleOf (linearCocycleForget c)) ∈ peuCocycleSubmodule I := by
  constructor
  · exact fun hc i => peuCocycle_coordinate χ b I c hc i
  · intro hc
    classical
    let ci (i : ι) := linearCocycleMap (characterCoordinateMap χ b i)
      (characterCoordinateMap_equivariant χ b i) (linearCocycleOf (linearCocycleForget c))
    let ei (i : ι) := linearCocycleMap (characterInclusionSemilinear (k := k) χ)
      (characterCoefficientInclusion_equivariant χ k) (ci i)
    have he : c = ∑ i, b i • ei i := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro g
      simp only [Submodule.coe_sum, Submodule.coe_smul,
        ContinuousMap.sum_apply, ContinuousMap.smul_apply]
      change c.1 g = ∑ i, b i * algebraMap F k (b.repr (c.1 g) i)
      simpa only [Algebra.smul_def, mul_comm] using (b.sum_repr (c.1 g)).symm
    rw [he]
    exact (peuCocycleSubmodule I).sum_mem fun i _ =>
      (peuCocycleSubmodule I).smul_mem (b i) (peuCocycle_inclusion χ b I (ci i) (hc i))

/-- The same coordinate criterion on the existing continuous splitting-class quotient. -/
theorem isPeuRamifiedClass_coordinates_iff (I : Subgroup G)
    (x : LinearContinuousClass k G (CharacterModule χ k)) :
    IsPeuRamifiedClass (k := k) I (linearClassEquiv x) ↔
      ∀ i, IsPeuRamifiedClass (k := F) I
        (linearClassEquiv (linearCharacterCoordinates χ b x i)) := by
  induction x using Quotient.inductionOn with | h c =>
    exact peuCocycle_coordinates_iff χ b I c

end LocalClassFieldTheory
