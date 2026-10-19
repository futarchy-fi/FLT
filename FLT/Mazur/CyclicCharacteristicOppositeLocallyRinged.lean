/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicChartResidualSections
public import FLT.Mazur.CyclicCharacteristicDisjointQuotientReduction

/-!
# The opposite normalized overlap over a characteristic orbit open

The original locally ringed projection on the opposite integer-invertible
open factors through the same characteristic orbit open. Its full morphism
agrees with the selected chart on each actual fppf transition source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Actual compatible tests give equality of locally ringed projections, not just orbit points. -/
theorem chartLocallyRingedProjection_related {T : Scheme} (b c : Bool)
    (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
    (h : UnmarkedRelated n b c q r) :
    q.toLRSHom ≫ chartLocallyRingedProjection n b =
      r.toLRSHom ≫ chartLocallyRingedProjection n c := by
  obtain ⟨a⟩ := h
  let k : ProductArrow n q r := productCompatibleParameter n b c q r a
  have he := congrArg (k.val.toLRSHom ≫ ·)
    (chartLocallyRingedProjection_condition n b c)
  rw [← Category.assoc, ← Category.assoc, ← Scheme.Hom.comp_toLRSHom,
    ← Scheme.Hom.comp_toLRSHom, productArrow_source, productArrow_target] at he
  exact he

/-- The ambient locally ringed projection on the opposite overlap. -/
def oppositeLocallyRingedProjection (b : Bool) :
    (transitionOpen n b).toScheme.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace n :=
  (transitionOpen n b).ι.toLRSHom ≫ chartLocallyRingedProjection n b

/-- The opposite overlap retains its original full orbit point. -/
theorem oppositeLocallyRingedProjection_base (b : Bool) (x : (transitionOpen n b).toScheme) :
    (oppositeLocallyRingedProjection n b).base x = chartProjection n b x.val := by
  change (chartLocallyRingedProjection n b).base _ = _
  rw [chartLocallyRingedProjection_base]
  rfl

/-- Its locally ringed factor into the selected characteristic orbit open. -/
def oppositeToInvariantOpen (b : Bool) :
    (transitionOpen n b).toScheme.toLocallyRingedSpace ⟶
      invariantOpenSpace n (integerOpen n (chartInteger (!b))) :=
  LocallyRingedSpace.IsOpenImmersion.lift
    ((invariantLocallyRingedSpace n).ofRestrict
      (integerOpen n (chartInteger (!b))).isOpenEmbedding)
    (oppositeLocallyRingedProjection n b) (by
      rintro _ ⟨x, rfl⟩
      have hx : chartProjection n b x.val ∈ integerOpen n (chartInteger (!b)) :=
        (mem_integerOpen_iff n (chartInteger (!b)) b x.val).mpr x.property
      exact ⟨⟨chartProjection n b x.val, hx⟩,
        (oppositeLocallyRingedProjection_base n b x).symm⟩)

/-- The opposite factor retains the entire ambient projection. -/
@[reassoc] theorem oppositeToInvariantOpen_comp (b : Bool) :
    oppositeToInvariantOpen n b ≫ (invariantLocallyRingedSpace n).ofRestrict
      (integerOpen n (chartInteger (!b))).isOpenEmbedding =
        oppositeLocallyRingedProjection n b :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- The transition square commutes as locally ringed morphisms, including regular functions. -/
theorem oppositeToInvariantOpen_transition (b : Bool) (i : (transitionCover n b).I₀) :
    ((transitionCover n b).f i).toLRSHom ≫ oppositeToInvariantOpen n b =
      (transitionTarget n b i).toLRSHom ≫ chartToInvariantOpen n (!b) := by
  rw [← cancel_mono ((invariantLocallyRingedSpace n).ofRestrict
    (integerOpen n (chartInteger (!b))).isOpenEmbedding)]
  simp only [Category.assoc, oppositeToInvariantOpen_comp, chartToInvariantOpen_comp]
  change ((transitionCover n b).f i).toLRSHom ≫
    (transitionOpen n b).ι.toLRSHom ≫ chartLocallyRingedProjection n b = _
  rw [← Category.assoc, ← Scheme.Hom.comp_toLRSHom]
  exact (chartLocallyRingedProjection_related n (!b) b _ _
    (transition_unmarkedRelated n b i)).symm

end FLT.Mazur.CyclicCharacteristicOrbit
