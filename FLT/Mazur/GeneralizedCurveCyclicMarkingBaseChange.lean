/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCyclicSubgroupPullbackComparison
public import FLT.Mazur.GroupSectionBaseChange
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# Original faithful cyclic markings under arbitrary base change

All cyclic sections pull back by the canonical monoidal unit map. Universal
distinctness follows from the actual projection on every test scheme, and the
reconstructed subgroup retains its original compatible comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve
open GroupSectionBaseChange UniversallyDistinctSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) {E : GeneralizedEllipticCurve S} {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- Pull back the entire original cyclic homomorphism. -/
def pullCyclicMarking : Multiplicative (ZMod n) →* (𝟙_ (Over T) ⟶ (E.baseChange g).group) where
  toFun i := pullSection g (φ i)
  map_one' := by simp only [map_one, pullSection, Functor.map_one, comp_one]
  map_mul' i j := by simp only [map_mul, pullSection, Functor.map_mul, comp_mul]

/-- Each cyclic section retains its original scheme map after projection. -/
@[reassoc] theorem pullCyclicMarking_fst (i : Multiplicative (ZMod n)) :
    (pullCyclicMarking g φ i).left ≫ pullback.fst E.group.hom g = g ≫ (φ i).left :=
  section_fst g (φ i)

/-- Universal distinctness survives every base change, with no reducedness assumption. -/
theorem pullCyclicMarking_distinct
    (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i))) :
    UniversallyDistinct (fun i : ZMod n ↦ pullCyclicMarking g φ (.ofAdd i)) := by
  intro V k hV i j hij
  let V' : Over S := (Over.map g).obj V
  let k' : V' ⟶ 𝟙_ (Over S) := Over.homMk (V.hom ≫ g) (Category.comp_id _)
  apply hφ V' k' hV
  apply Over.OverMorphism.ext
  have hh := congrArg (fun f ↦ f.left ≫ pullback.fst E.group.hom g) hij
  simp only [Over.comp_left, Category.assoc, pullCyclicMarking_fst] at hh
  have hk : k.left = V.hom := by simpa using k.w
  simpa only [Over.comp_left, Over.homMk_left, k', hk, Category.assoc] using hh

variable [NeZero n] (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))

/-- Reconstruction from pulled sections is the actual pullback subgroup. -/
def pullCyclicMarkingCompatibleIso :
    FiniteSubgroup.CompatibleIso
      ((E.baseChange g).relativeCyclicSubgroup (pullCyclicMarking g φ)
        (pullCyclicMarking_distinct g φ hφ)) ((E.relativeCyclicSubgroup φ hφ).baseChange g) :=
  relativeCyclicSubgroupPullbackCompatibleIso g φ (pullCyclicMarking g φ) hφ
    (pullCyclicMarking_distinct g φ hφ) (Iso.refl _) (fun _ ↦ Category.comp_id _)

/-- Retain a previously constructed comparison to the original finite subgroup. -/
def pullCyclicMarkingOriginalIso (H : E.FiniteSubgroup n)
    (a : FiniteSubgroup.CompatibleIso (E.relativeCyclicSubgroup φ hφ) H) :
    FiniteSubgroup.CompatibleIso
      ((E.baseChange g).relativeCyclicSubgroup (pullCyclicMarking g φ)
        (pullCyclicMarking_distinct g φ hφ)) (H.baseChange g) :=
  (pullCyclicMarkingCompatibleIso g φ hφ).trans (a.baseChange g)

end FLT.Mazur.GeneralizedEllipticCurve
