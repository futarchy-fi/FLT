/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PureAction
public import FLT.GaloisRepresentation.HardlyRamified.ThreeGroupLocalUnramified
public import FLT.GaloisRepresentation.HardlyRamified.TrivialPrimeFiltration

/-!
# Purity of filtered point actions unramified away from two

The arithmetic part of the constant-filtration argument is proved here.
Trivial three-torsion graded pieces force a three-group action image. Its local
inertia at two is trivial, so unramifiedness away from two makes the whole action
everywhere unramified and therefore trivial.

The hypothesis `UnramifiedOutside {2}` is retained explicitly: deducing it from
a finite-flat group-scheme filtration by constant groups requires the geometric
étaleness and specialization theorems, which are not asserted in this file.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan
namespace FiniteContinuousGaloisModule

/-- A finite rational point action with three-group image kills dyadic inertia. -/
theorem inertia_two_trivial_of_threeGroup (W : FiniteContinuousGaloisModule)
    (hW : IsPGroup 3 (MulAction.toPermHom
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) W).range) :
    ∀ σ ∈ localInertiaGroup twoAdicPlace, ∀ w : W,
      Field.absoluteGaloisGroup.map
        (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ • w = w := by
  let ρ := MulAction.toPermHom (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) W
  let φ := Field.absoluteGaloisGroup.map
    (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ))
  let f := ρ.rangeRestrict.comp φ.toMonoidHom
  have hker : (f.ker : Set (Field.absoluteGaloisGroup
      (twoAdicPlace.adicCompletion ℚ))) =
      φ ⁻¹' (W.pointActionKernel : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
    ext σ
    change f σ = 1 ↔ ρ (φ σ) = 1
    exact Subtype.ext_iff
  have hf : IsOpen (f.ker : Set (Field.absoluteGaloisGroup
      (twoAdicPlace.adicCompletion ℚ))) := by
    rw [hker]
    exact W.pointActionKernel_isOpen.preimage φ.continuous
  have hI := localInertia_le_ker_of_threeGroup hW f hf
  intro σ hσ w
  have hp : ρ (φ σ) = 1 := congrArg Subtype.val (hI hσ)
  exact Equiv.congr_fun hp w

/-- A trivially three-filtered finite rational action unramified away from two
is pointwise trivial. This does not assume that the filtration splits. -/
theorem pure_one_of_trivialThreeFiltration (W : FiniteContinuousGaloisModule)
    (F : TrivialPrimeFiltration 3
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) W)
    (hur : UnramifiedOutside {2} W) :
    Pure W (1 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℤ) := by
  apply W.pure_one_of_everywhere_unramified
  constructor
  intro q hq _ σ hσ w
  by_cases hq2 : q = 2
  · subst q
    exact W.inertia_two_trivial_of_threeGroup F.isPGroup_range σ hσ w
  · exact hur.inertia_trivial q hq (by simpa) σ hσ w

end FiniteContinuousGaloisModule
end ThreeAdicPlan
