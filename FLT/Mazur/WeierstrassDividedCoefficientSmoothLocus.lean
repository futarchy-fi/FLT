/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCoefficientSmoothRecovery

/-!
# The original coefficient smooth orbit inside the tensor model smooth locus

Lift the independently retained original smooth scheme, including its original
zero section, through the actual relative smooth-open inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "g" => (pullback.fst q (finiteGlobalStructure hπ data j hj) :
  finiteGlobalTensorModel hπ data S j hj ⟶ Spec (.of S))
local notation "B" => finiteGlobalSmoothCoefficientEmbedding S hπ data j hj
variable [LocallyOfFinitePresentation
  (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (finiteGlobalStructure hπ data j hj))]

/-- The full original smooth orbit as an open subscheme of the actual model smooth locus. -/
def finiteGlobalCoefficientSmoothOrbitToSmooth :
    (integralSmoothOpen V).toScheme ⟶ (g).smoothLocus.toScheme :=
  IsOpenImmersion.lift (g).smoothLocus.ι B (by
    rw [Scheme.Opens.range_ι]
    let _ : Smooth (B ≫ g) := by
      rw [finiteGlobalSmoothCoefficientEmbedding_structure]
      infer_instance
    have h := Scheme.Hom.preimage_smoothLocus_eq B g
    rw [Scheme.Hom.smoothLocus_eq_top (B ≫ g)] at h
    rintro _ ⟨x, rfl⟩
    exact h.ge (Set.mem_univ x))

/-- Inclusion retains exactly the independently constructed original smooth embedding. -/
@[reassoc] theorem finiteGlobalCoefficientSmoothOrbitToSmooth_inclusion :
    finiteGlobalCoefficientSmoothOrbitToSmooth hπ data S j hj ≫ (g).smoothLocus.ι = B :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original zero section, now lying in the full actual model smooth locus. -/
def finiteGlobalOriginalCoefficientSmoothZero : Spec (.of S) ⟶ (g).smoothLocus.toScheme :=
  integralSmoothZero V ≫ finiteGlobalCoefficientSmoothOrbitToSmooth hπ data S j hj

/-- Its inclusion is still the retained original zero, without choosing polygon coordinates. -/
@[reassoc] theorem finiteGlobalOriginalCoefficientSmoothZero_inclusion :
    finiteGlobalOriginalCoefficientSmoothZero hπ data S j hj ≫ (g).smoothLocus.ι =
      integralSmoothZero V ≫ B := by
  rw [finiteGlobalOriginalCoefficientSmoothZero, Category.assoc,
    finiteGlobalCoefficientSmoothOrbitToSmooth_inclusion]

end FLT.Mazur.WeierstrassDividedDepth
