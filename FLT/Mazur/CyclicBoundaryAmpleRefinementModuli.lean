/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeRefinement
public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeModuli
public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeAction

/-!
# Base refinements preserve the full ample modular family and finite action

The actual parameter refinement is cartesian and carries a compatible
isomorphism of the full universal curves and subgroups. The modular map and
finite relabeling action commute on all scheme tests.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n] (g : T ⟶ S) (h : U ⟶ S) (f : U ⟶ T) (w : f ≫ g = h)

local instance ampleRefinementModuliPullbackGroup_separated {V : Scheme} (a : V ⟶ S) :
    IsSeparated (E.baseChange a).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom a))

local instance ampleRefinementModuliPullbackGroup_smooth {V : Scheme} (a : V ⟶ S) :
    SmoothOfRelativeDimension 1 (E.baseChange a).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom a
    inferInstance

local notation "r" => ampleBaseRefinement E n g h f w

/-- Every supplied base refinement gives the actual cartesian parameter comparison. -/
theorem ampleBaseRefinement_isPullback :
    IsPullback (r) (ampleParameterBase (E.baseChange h) n)
      (ampleParameterBase (E.baseChange g) n) f := by
  apply IsPullback.of_right (h₁₂ := ampleBaseChangeToOriginal g E n)
    (h₂₂ := g)
  · simpa only [ampleBaseRefinement_original, w] using
      ampleBaseChangeToOriginal_isPullback h E n
  · exact ampleBaseRefinement_base E n g h f w
  · exact ampleBaseChangeToOriginal_isPullback g E n

/-- Refinement preserves the actual universal ample subgroup and its full generalized curve. -/
def ampleBaseRefinementSubgroupIso :
    CompatibleIso (ampleUniversalLevel (E.baseChange h) n).val.2
      ((ampleUniversalLevel (E.baseChange g) n).val.2.baseChange (r)) := by
  let c := ((ampleBaseChangeSubgroupIso g E n).baseChange (r)).trans
    ((ampleUniversalLevel E n).val.2.compatibleBaseChangeComp
      (ampleBaseChangeToOriginal g E n) (r)).symm
  rw [ampleBaseRefinement_original] at c
  exact (ampleBaseChangeSubgroupIso h E n).trans c.symm

/-- The universal ample class is retained by the actual refinement. -/
theorem ampleUniversalClass_baseRefinement :
    ampleUniversalClass (E.baseChange h) n =
      ampleCyclicClassesPullback (r) n (ampleUniversalClass (E.baseChange g) n) :=
  Quotient.sound ⟨ampleBaseRefinementSubgroupIso E n g h f w⟩

/-- The full modular transformation commutes with each actual base refinement. -/
theorem ampleModuliMap_baseRefinement :
    ampleModuliMap (E.baseChange h) n =
      uliftYoneda.map (r) ≫ ampleModuliMap (E.baseChange g) n := by
  ext V v
  change ampleCyclicClassesPullback v.down n (ampleUniversalClass (E.baseChange h) n) =
    ampleCyclicClassesPullback (v.down ≫ (r)) n (ampleUniversalClass (E.baseChange g) n)
  rw [ampleUniversalClass_baseRefinement E n g h f w, ampleCyclicClassesPullback_comp]
  rfl

/-- The actual refinement is equivariant for the common finite relabeling group. -/
@[reassoc] theorem ampleBaseRefinement_relabel (e : RelabelGroup n) :
    (r) ≫ ampleRelabel (E.baseChange g) n e =
      ampleRelabel (E.baseChange h) n e ≫ (r) := by
  apply (ampleBaseChangeToOriginal_isPullback g E n).hom_ext
  · rw [Category.assoc, ← ampleBaseChangeToOriginal_relabel,
      ampleBaseRefinement_original_assoc, Category.assoc, ampleBaseRefinement_original,
      ampleBaseChangeToOriginal_relabel]
  · rw [Category.assoc, ampleRelabel_base, ampleBaseRefinement_base,
      Category.assoc, ampleBaseRefinement_base, ampleRelabel_base_assoc]

end FLT.Mazur.CyclicBoundaryParameter
