/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertSplitFunctions
public import FLT.Mazur.SmoothHilbertSheafQuotient
public import Mathlib.CategoryTheory.Sites.PreservesLimits

/-!
# The represented fppf quotient of the original split chart relation

The same target scheme represents the coequalizer in the original fppf sheaf
category. Its map to the original relative Picard sheaf is the original chart
map. This identifies the full chart quotient, not the global Picard quotient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [IsOpenImmersion V.hom] (c : (relativeFppfSheaf f).obj.obj (op V))
  (s : V ⟶ W) (hs : s ≫ b = 𝟙 V)
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "J" => GrothendieckTopology.over Scheme.fppfTopology (Spec (CommRingCat.of R))

/-- The original variable chart map considered in the original fppf sheaf category. -/
def variableHilbertPicardSheafMap (T : Over (Spec (.of R)))
    (t : (relativeFppfSheaf f).obj.obj (op T)) :
    ((J).uliftYoneda.{1}).obj (variableHilbertTest f d T) ⟶ smoothHilbertTargetSheaf f :=
  ⟨variableHilbertPicardMap f d hL T t⟩

omit [IsOpenImmersion V.hom] in
include hs in
/-- The actual split comparison is an effective epimorphism of represented fppf sheaves. -/
theorem variableHilbertSplitSheaf_effectiveEpi :
    EffectiveEpi (((J).uliftYoneda.{1}).map (baseMarkedChartChange f b d)) := by
  let _ : IsSplitEpi (((J).uliftYoneda.{1}).map (baseMarkedChartChange f b d)) := IsSplitEpi.mk'
    ⟨((J).uliftYoneda.{1}).map (baseMarkedChartChange f s d), by
      rw [← Functor.map_comp, variableHilbertChange_section f d b s hs,
        CategoryTheory.Functor.map_id]⟩
  infer_instance

/-- The unchanged full chart relation is the represented sheaf kernel pair. -/
theorem variableHilbertSplitSheaf_isPullback :
    IsPullback (((J).uliftYoneda.{1}).map (variableChartRelationFst f hL d W cW))
      (((J).uliftYoneda.{1}).map (variableChartRelationSnd f hL d W cW))
      (((J).uliftYoneda.{1}).map (baseMarkedChartChange f b d))
      (((J).uliftYoneda.{1}).map (baseMarkedChartChange f b d)) :=
  (variableHilbertChange_isPullback f hL d b c).map ((J).uliftYoneda.{1})

/-- The target scheme represents the fppf coequalizer of the original full chart relation. -/
def variableHilbertSplitSheafCoforkIsColimit :
    IsColimit (Cofork.ofπ (((J).uliftYoneda.{1}).map (baseMarkedChartChange f b d))
      (variableHilbertSplitSheaf_isPullback f hL d b c).w) := by
  let _ := variableHilbertSplitSheaf_effectiveEpi f d b s hs
  exact isColimitCoforkOfEffectiveEpi (((J).uliftYoneda.{1}).map (baseMarkedChartChange f b d)) _
    (variableHilbertSplitSheaf_isPullback f hL d b c).isLimit

omit [IsOpenImmersion V.hom] in
/-- The coequalizer-to-Picard map is the original chart map on every original relative test. -/
theorem variableHilbertSplitSheaf_picard :
    ((J).uliftYoneda.{1}).map (baseMarkedChartChange f b d) ≫
      variableHilbertPicardSheafMap f hL d V c =
      variableHilbertPicardSheafMap f hL d W cW := by
  apply (sheafToPresheaf _ (Type 1)).map_injective
  ext T k
  exact baseMarkedChartChange_class f hL b (d, c) k.down

/-- The represented quotient embeds into the original Picard sheaf on every original test. -/
instance variableHilbertPicardSheafMap_mono :
    Mono (variableHilbertPicardSheafMap f hL d V c) := by
  have hm : Mono (variableHilbertPicardMap f d hL V c) := by
    suffices ∀ T, Mono ((variableHilbertPicardMap f d hL V c).app T) from
      NatTrans.mono_of_mono_app _
    intro T
    rw [CategoryTheory.mono_iff_injective]
    intro k l hkl
    apply ULift.ext
    exact baseOpenHilbertPoint_injective f hL d V c T.unop hkl
  exact (sheafToPresheaf _ (Type 1)).mono_of_mono_map hm

end FLT.Mazur.HilbertChart
