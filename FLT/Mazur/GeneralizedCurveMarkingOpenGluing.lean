/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingAffineRange
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Actual open gluing of the original marked cubic charts

Affine marking neighborhoods and exact restriction images prove local
directedness. The resulting colimit is an actual scheme, with open chart
inclusions and a structure map to the original locally Noetherian base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
open MonoidalCategory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group)

/-- Actual affine frame refinements make the cubic diagram locally directed. -/
instance smoothMarkingAffineDiagram_locallyDirected :
    (smoothMarkingAffineDiagram E s ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j k fi fj xi xj heq
  change (smoothMarkingAffineDiagram E s).map fi xi =
    (smoothMarkingAffineDiagram E s).map fj xj at heq
  have hb : smoothMarkingAffineBase E s i xi = smoothMarkingAffineBase E s j xj := by
    have hh := congrArg (smoothMarkingAffineBase E s k) heq
    simpa only [← Scheme.Hom.comp_apply, smoothMarkingAffineBase_naturality] using hh
  have hx : smoothMarkingAffineBase E s i xi ∈ i.base.1 ⊓ j.base.1 :=
    ⟨smoothMarkingAffineBase_mem E s i xi, hb.symm ▸ smoothMarkingAffineBase_mem E s j xj⟩
  obtain ⟨l, hl, hle⟩ := exists_smoothMarkingAffineChart E s hx
  let fli : l ⟶ i := homOfLE (hle.trans inf_le_left)
  let flj : l ⟶ j := homOfLE (hle.trans inf_le_right)
  have hr : xi ∈ Set.range ((smoothMarkingAffineDiagram E s).map fli) := by
    rw [smoothMarkingAffineDiagram_range]
    exact hl
  obtain ⟨x, hx⟩ := hr
  refine ⟨l, fli, flj, x, hx, ?_⟩
  change (smoothMarkingAffineDiagram E s).map flj x = xj
  apply ((smoothMarkingAffineDiagram E s).map fj).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
  have hf : flj ≫ fj = fli ≫ fi := Subsingleton.elim _ _
  rw [hf, Functor.map_comp, Scheme.Hom.comp_apply, hx]
  exact heq

/-- The original marking charts glue to a scheme by their constructed open restriction maps. -/
def smoothMarkingGluedCubic : Scheme := Limits.colimit (smoothMarkingAffineDiagram E s)

/-- Each actual affine cubic chart has its canonical inclusion into the glued scheme. -/
def smoothMarkingGluedChart (i : SmoothMarkingAffineChart E s) :
    (smoothMarkingAffineDiagram E s).obj i ⟶ smoothMarkingGluedCubic E s :=
  Limits.colimit.ι (smoothMarkingAffineDiagram E s) i

/-- The glued chart inclusions are open immersions. -/
instance smoothMarkingGluedChart_isOpenImmersion (i : SmoothMarkingAffineChart E s) :
    IsOpenImmersion (smoothMarkingGluedChart E s i) := by
  unfold smoothMarkingGluedChart
  infer_instance

/-- Constructed restriction maps recover the same chart inclusion. -/
@[reassoc] theorem smoothMarkingGluedChart_naturality
    {i j : SmoothMarkingAffineChart E s} (f : i ⟶ j) :
    (smoothMarkingAffineDiagram E s).map f ≫ smoothMarkingGluedChart E s j =
      smoothMarkingGluedChart E s i := Limits.colimit.w _ f

/-- The actual whole-base cocone descends to a structure map of the glued cubic. -/
def smoothMarkingGluedBase : smoothMarkingGluedCubic E s ⟶ S :=
  Limits.colimit.desc (smoothMarkingAffineDiagram E s)
    { pt := S
      ι := { app := smoothMarkingAffineBase E s
             naturality := by
               intro i j f
               exact (smoothMarkingAffineBase_naturality E s f).trans
                 (Category.comp_id _).symm } }

/-- The global structure map recovers the original base morphism on every cubic chart. -/
@[reassoc] theorem smoothMarkingGluedChart_base (i : SmoothMarkingAffineChart E s) :
    smoothMarkingGluedChart E s i ≫ smoothMarkingGluedBase E s =
      smoothMarkingAffineBase E s i := Limits.colimit.ι_desc _ i

/-- The actual affine marking cubics cover the glued scheme. -/
theorem smoothMarkingGluedChart_jointly_surjective (x : smoothMarkingGluedCubic E s) :
    ∃ (i : SmoothMarkingAffineChart E s) (y : (smoothMarkingAffineDiagram E s).obj i),
      smoothMarkingGluedChart E s i y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective (smoothMarkingAffineDiagram E s) x

end FLT.Mazur.GeneralizedEllipticCurve
