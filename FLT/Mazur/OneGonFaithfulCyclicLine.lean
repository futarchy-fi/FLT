/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFaithfulCompleteDivisor
public import FLT.Mazur.CartierIdealPullbackComparison
public import FLT.Mazur.DivisorBaseChangeRank

/-!
# The positive line of the actual complete cyclic subgroup

Dualizing the whole subgroup ideal gives its positive divisor line. Arbitrary
base change retains the actual Cartier divisor and its canonical line, and
every nonempty base retains nonempty divisor support.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "f" => Over.hom (family (PowerSeries.X : PowerSeries K))
local notation "I" => faithfulCompleteIdeal K n labels hlabels

/-- The positive divisor line of the entire actual cyclic subgroup. -/
def faithfulCompleteCyclicLine : (family (t)).left.Modules :=
  divisorLineBundle (I) (faithfulCompleteIdeal_cartier K n labels hlabels).1

/-- The actual cyclic divisor line has rank one. -/
theorem faithfulCompleteCyclicLine_rankOne :
    LocallyFreeRankOne (faithfulCompleteCyclicLine K n labels hlabels) :=
  (faithfulCompleteIdeal_cartier K n labels hlabels).1.divisorLineBundle_locallyFreeRankOne

variable {T : Scheme} (g : T ⟶ Spec (.of (PowerSeries K)))

/-- The full cyclic divisor remains Cartier after every scheme base change. -/
theorem faithfulCompleteIdeal_baseChange_cartier :
    RelativeEffectiveCartier (pullback.snd (f) g) ((I).comap (pullback.fst (f) g)) :=
  relativeCartierBaseChange _ _ _ (faithfulCompleteIdeal_cartier K n labels hlabels)

/-- The full pulled-back divisor subscheme is finite over the unchanged test base. -/
theorem faithfulCompleteIdeal_baseChange_finite :
    IsFinite (((I).comap (pullback.fst (f) g)).subschemeι ≫ pullback.snd (f) g) := by
  let _ := faithfulCompleteIdeal_finite K n labels hlabels
  exact isFinite_divisor_baseChange _ _ _

/-- The canonical pullback comparison identifies the actual positive cyclic divisor lines. -/
def faithfulCompleteCyclicLineBaseChangeIso :
    (Scheme.Modules.pullback (pullback.fst (f) g)).obj
        (faithfulCompleteCyclicLine K n labels hlabels) ≅
      divisorLineBundle ((I).comap (pullback.fst (f) g))
        (faithfulCompleteIdeal_baseChange_cartier K n labels hlabels g).1 :=
  divisorLinePullbackIsoOfCartier _ (faithfulCompleteIdeal_cartier K n labels hlabels).1
    (faithfulCompleteIdeal_baseChange_cartier K n labels hlabels g).1

/-- Every nonempty test retains a point of the whole cyclic divisor. -/
theorem faithfulCompleteIdeal_baseChange_nonempty [Nonempty T] :
    (((I).comap (pullback.fst (f) g)).support : Set (pullback (f) g : Scheme)).Nonempty := by
  let _ := family_proper (t)
  let z (i : ZMod n) :=
    (faithfulCompleteMarking K n labels hlabels (.ofAdd i) ≫ relativeGroupInclusion (t)).left
  have hz (i : ZMod n) : z i ≫ (f) = 𝟙 _ :=
    (faithfulCompleteMarking K n labels hlabels (.ofAdd i) ≫ relativeGroupInclusion (t)).w
  have he : (I).comap (pullback.fst (f) g) =
      ∏ i : ZMod n, (sectionBaseChange (f) g (z i) (hz i)).ker := by
    rw [faithfulCompleteIdeal_product]
    exact section_prod_comap_eq (f) g Finset.univ z hz
  rw [he]
  obtain ⟨x⟩ := ‹Nonempty T›
  refine ⟨sectionBaseChange (f) g (z 0) (hz 0) x, ?_⟩
  apply (mem_support_prod Finset.univ _ _).mpr
  refine ⟨0, Finset.mem_univ _, ?_⟩
  rw [← SetLike.mem_coe, support_section_ker (pullback.snd (f) g) _
    (sectionBaseChange_snd (f) g (z 0) (hz 0))]
  exact ⟨x, rfl⟩

end FLT.Mazur.OneGonSmoothing
