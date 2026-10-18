/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingRelativeGroup
public import FLT.Mazur.FaithfulMarkingPullbackSections
public import FLT.Mazur.ConstantCyclicRelativeClosed

/-!
# Actual finite cyclic subgroups on the complete one-gon parameter scheme

Use the faithful cyclic-marking open of the smooth group over the entire
smoothing base. Its universal sections construct a finite etale subgroup of
rank n, with a closed embedding in the original proper cubic. No existence
of a lift of an arbitrary closed-fiber parameter is asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open AuxiliaryLevel UniversallyDistinctSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (t : R) (n : ℕ) [NeZero n]

/-- Faithful cyclic markings on the smooth group of the entire original family. -/
def relativeCyclicParameter : Over (Spec (.of R)) :=
  faithfulScheme (relativeGroup t).X (Multiplicative (ZMod n))

variable {T : Scheme} (g : T ⟶ Spec (.of R))
  (f : Over.mk g ⟶ relativeCyclicParameter t n)

/-- The parameter's actual homomorphism into sections of the pulled-back group. -/
def relativeCyclicMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over T) ⟶ (relativeTestGroup t g).X) :=
  faithfulSectionMarking (relativeGroup t).X (Multiplicative (ZMod n)) g f

/-- Every such test has universally distinct cyclic labels, with no added hypothesis. -/
theorem relativeCyclicMarking_distinct :
    UniversallyDistinct (fun i : ZMod n ↦ relativeCyclicMarking t n g f (.ofAdd i)) := by
  intro V k hV i j hij
  have he := faithfulSectionMarking_distinct
    (relativeGroup t).X (Multiplicative (ZMod n)) g f V k hV hij
  exact congrArg Multiplicative.toAdd he

/-- The actual rank-n group maps to the smooth group by its original cyclic labels. -/
def relativeCyclicInclusion : ConstantCyclicGroup.model T n ⟶ (relativeTestGroup t g).X :=
  ConstantCyclicSectionMap.toScheme (relativeCyclicMarking t n g f)

/-- The constructed inclusion preserves multiplication and identity. -/
instance relativeCyclicInclusion_isMonHom : IsMonHom (relativeCyclicInclusion t n g f) :=
  ConstantCyclicSectionMap.toScheme_isMonHom _

/-- Faithfulness makes the actual group homomorphism a closed subgroup embedding. -/
instance relativeCyclicInclusion_closed :
    IsClosedImmersion (relativeCyclicInclusion t n g f).left :=
  ConstantCyclicRelativeClosed.toScheme_closed _ (relativeCyclicMarking_distinct t n g f)

/-- The subgroup retains its embedding in the whole original cubic, not just its smooth open. -/
def relativeCyclicCurveMap :
    ConstantCyclicGroup.model T n ⟶ (Over.pullback g).obj (family t) :=
  relativeCyclicInclusion t n g f ≫ relativeTestInclusion t g

/-- The cyclic subgroup is closed in the entire proper curve. -/
theorem relativeCyclicCurveMap_closed :
    IsClosedImmersion (relativeCyclicCurveMap t n g f).left := by
  let _ := relativeTestFamily_proper t g
  let d := relativeCyclicCurveMap t n g f
  apply ConstantCyclicRelativeClosed.closed d
  intro V k hV i j hij
  apply relativeCyclicMarking_distinct t n g f V k hV
  have : Mono (relativeTestInclusion t g) := Over.mono_of_mono_left _
  apply (cancel_mono (relativeTestInclusion t g)).mp
  simpa only [d, relativeCyclicCurveMap, relativeCyclicInclusion, Category.assoc,
    ConstantCyclicSectionMap.component_toScheme_assoc] using hij

/-- The subgroup has degree n on every original test base. -/
theorem relativeCyclic_degree :
    FCurve.FiniteLocallyFreeDegree (ConstantCyclicGroup.model T n).hom n :=
  ConstantCyclicRelativeGeometry.degree T n

/-- The actual constructed subgroup is etale over its test base. -/
theorem relativeCyclic_etale : Etale (ConstantCyclicGroup.model T n).hom :=
  ConstantCyclicRelativeGeometry.etale T n

end FLT.Mazur.OneGonSmoothing
