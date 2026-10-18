/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicFiniteTypeAtlas
public import FLT.Mazur.FiniteGroupNeighborhoodAffineCover

/-!
# The combined finite invariant affine characteristic cover

Both actual normalized subgroup loci have finite invariant affine covers for
the same relabeling group. Their combined finite index retains the original
characteristic choice, chart inclusion, action and finite type map to Spec Z.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The finite invariant affine cover of each actual normalized characteristic locus. -/
def invariantAffineCover (b : Bool) : (normalizedLocus n b).OpenCover :=
  FiniteGroupNeighborhoodCover.finiteCover (normalizedRelabelAction n b)
    (normalizedLocus_hasFiniteNeighborhoods n b)

/-- Each characteristic cover has finitely many actual charts. -/
instance invariantAffineCoverFintype (b : Bool) : Fintype (invariantAffineCover n b).I₀ := by
  unfold invariantAffineCover
  infer_instance

/-- The combined index remembers which original characteristic locus is covered. -/
abbrev InvariantAffineIndex := (b : Bool) × (invariantAffineCover n b).I₀

/-- The two characteristic covers together still have finitely many charts. -/
instance invariantAffineIndexFintype : Fintype (InvariantAffineIndex n) := inferInstance

/-- An actual affine chart in the combined cover. -/
def invariantAffineChart (i : InvariantAffineIndex n) : Scheme :=
  (invariantAffineCover n i.1).X i.2

/-- Every combined chart is affine. -/
instance invariantAffineChart_isAffine (i : InvariantAffineIndex n) :
    IsAffine (invariantAffineChart n i) :=
  FiniteGroupNeighborhoodCover.finiteCover_isAffine _ _ i.2

/-- The original open inclusion into the normalized characteristic locus. -/
def invariantAffineInclusion (i : InvariantAffineIndex n) :
    invariantAffineChart n i ⟶ normalizedLocus n i.1 :=
  (invariantAffineCover n i.1).f i.2

/-- The combined chart maps are open immersions. -/
instance invariantAffineInclusion_isOpenImmersion (i : InvariantAffineIndex n) :
    IsOpenImmersion (invariantAffineInclusion n i) := by
  unfold invariantAffineInclusion
  infer_instance

/-- The original common relabeling group acts on every selected affine chart. -/
def invariantAffineAction (i : InvariantAffineIndex n) :
    RelabelGroup n →* Aut (invariantAffineChart n i) :=
  FiniteGroupNeighborhoodCover.finiteAction _ _ i.2

/-- The chart action retains the exact original relabeling action. -/
@[reassoc] theorem invariantAffineAction_inclusion (i : InvariantAffineIndex n)
    (e : RelabelGroup n) :
    (invariantAffineAction n i e).hom ≫ invariantAffineInclusion n i =
      invariantAffineInclusion n i ≫ (normalizedRelabelAction n i.1 e).hom :=
  FiniteGroupNeighborhoodCover.finiteAction_inclusion _ _ i.2 e

/-- Every point in either actual normalized locus belongs to a selected invariant chart. -/
theorem invariantAffineCover_covers (b : Bool) (x : normalizedLocus n b) :
    ∃ i : (invariantAffineCover n b).I₀,
      x ∈ Set.range (invariantAffineInclusion n ⟨b, i⟩) :=
  (invariantAffineCover n b).exists_eq x

/-- The actual integer structure map on each selected affine chart. -/
def invariantAffineToInt (i : InvariantAffineIndex n) :
    invariantAffineChart n i ⟶ Spec (.of ℤ) :=
  invariantAffineInclusion n i ≫ normalizedLocusToInt n i.1

/-- Each selected invariant affine chart is locally of finite type over the integers. -/
instance invariantAffineToInt_locallyOfFiniteType (i : InvariantAffineIndex n) :
    LocallyOfFiniteType (invariantAffineToInt n i) := by
  unfold invariantAffineToInt
  infer_instance

/-- Affineness makes each selected invariant parameter chart quasi-compact over the integers. -/
instance invariantAffineToInt_quasiCompact (i : InvariantAffineIndex n) :
    QuasiCompact (invariantAffineToInt n i) :=
  (HasAffineProperty.iff_of_isAffine
    (Q := fun X _ _ _ => CompactSpace X)).mpr inferInstance

end FLT.Mazur.CyclicCharacteristicAtlas
