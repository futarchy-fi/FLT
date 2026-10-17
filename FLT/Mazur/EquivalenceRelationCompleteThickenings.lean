/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteClosedLocus
public import FLT.Mazur.EquivalenceRelationCompleteSourceRestriction
public import FLT.Mazur.EquivalenceRelationNormalizedFrameLifts
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Full original relation comparisons on constructed complete thickenings

Every positive power of the complete-locus ideal defines an actual infinitesimal
source. Its full original two-endpoint relation has the scheme-level permutation
comparison. Every original endpoint has a lift to each order of some such source.
These closed thickenings do not supply original open lifting neighborhoods.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (I : Type) [Fintype I] (o : I)

/-- The actual ideal of the closed original complete locus. -/
def completeSupportIdeal : (source p q I o).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨completePointLocus (p := p) (q := q) I o, completePointLocus_isClosed I o⟩

/-- The complete-locus infinitesimal source at every positive ideal power. -/
def completeThickening (k : ℕ) : Scheme :=
  (completeSupportIdeal (p := p) (q := q) I o ^ (k + 1)).subscheme

/-- Its unchanged closed source inclusion. -/
def completeThickeningInclusion (k : ℕ) :
    completeThickening (p := p) (q := q) I o k ⟶ source p q I o :=
  (completeSupportIdeal (p := p) (q := q) I o ^ (k + 1)).subschemeι

instance completeThickeningInclusion_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (completeThickeningInclusion (p := p) (q := q) I o k) :=
  inferInstanceAs (IsClosedImmersion
    (completeSupportIdeal (p := p) (q := q) I o ^ (k + 1)).subschemeι)

/-- Each stage retains precisely the original complete support, including noninterior points. -/
theorem completeThickeningInclusion_range (k : ℕ) :
    Set.range (completeThickeningInclusion (p := p) (q := q) I o k) =
      completePointLocus (p := p) (q := q) I o := by
  change Set.range (completeSupportIdeal (p := p) (q := q) I o ^ (k + 1)).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow_succ]
  rfl

variable (e : CategoryTheory.EquivalenceRelation p q)

/-- The entire original relation over a constructed stage admits the permutation comparison. -/
def completeThickeningRelationIso (k : ℕ) {V : Scheme} (v : V ⟶ source p q I o) :
    SourceRestriction.comparisonSource e (completeThickeningInclusion I o k) v ≅
      SourceRestriction.relation (completeThickeningInclusion I o k) v :=
  SourceRestriction.comparisonIso e _ v (completeThickeningInclusion_range I o k).le

/-- Every arbitrary second source and original arrow is retained on each stage. -/
@[reassoc] theorem completeThickeningRelationIso_inv_arrow
    (k : ℕ) {V : Scheme} (v : V ⟶ source p q I o) :
    (completeThickeningRelationIso I o e k v).inv ≫
      pullback.fst (relationComparison e I o)
        (SourceRestriction.original (completeThickeningInclusion I o k) v) ≫
          relationComparison e I o ≫ relationArrow p q I o =
            SourceRestriction.arrow (completeThickeningInclusion I o k) v :=
  SourceRestriction.comparisonInverse_arrow e _ v (completeThickeningInclusion_range I o k).le

variable [QuasiCompact p]

include e in
/-- Every original point lifts to a constructed complete thickening of every order. -/
theorem exists_completeThickening_lift (x : A) (k : ℕ) :
    ∃ (n : ℕ) (j : Fin n) (y : completeThickening (p := p) (q := q) (Fin n) j k),
      (completeThickeningInclusion (Fin n) j k ≫ first p q (Fin n) j) y = x := by
  let K := AlgebraicClosure (A.residueField x)
  let g := Spec.map (CommRingCat.ofHom (algebraMap (A.residueField x) K))
  let b := g ≫ A.fromSpecResidueField x
  obtain ⟨n, j, u, hu, hc⟩ := exists_complete_normalized_lift e b
  have hm := (complete_iff_mem_completePointLocus (Fin n) j u).mp hc
  rw [← completeThickeningInclusion_range (Fin n) j k] at hm
  obtain ⟨y, hy⟩ := hm
  refine ⟨n, j, y, ?_⟩
  change first p q (Fin n) j (completeThickeningInclusion (Fin n) j k y) = x
  rw [hy, ← Scheme.Hom.comp_apply, hu]
  exact Scheme.fromSpecResidueField_apply x _

end FLT.Mazur.EquivalenceRelationNormalizedFrames
