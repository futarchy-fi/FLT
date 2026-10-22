/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankOneComparison

/-!
# The actual rank-one comparison as a full endpoint equalizer

The base change of the original comparison to a rank-one coefficient test
is isomorphic over that test to the equalizer of its boundary endpoints.
This computes the whole comparison scheme, rather than only its point set.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- Inverse maps over monic projections construct an isomorphism over the base. -/
def rankOneEqualizerIsoOfMonoProjections {X Y T : Scheme.{0}} (u : X ⟶ T) (v : Y ⟶ T)
    [Mono u] [Mono v] (a : X ⟶ Y) (b : Y ⟶ X) (ha : a ≫ v = u) (hb : b ≫ u = v) :
    X ≅ Y where
  hom := a
  inv := b
  hom_inv_id := by
    apply (cancel_mono u).mp
    rw [Category.assoc, hb, ha, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono v).mp
    rw [Category.assoc, ha, hb, Category.id_comp]

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData)
  (e : CategoryTheory.EquivalenceRelation p q) (hJ : J.comap p = J.comap q)
local instance oneEqualizerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance oneEqualizerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
variable (t : B ⟶ pullback
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
  (ht : Set.range (t ≫ pullback.fst _ _ ≫ J.subschemeι) ⊆ rankAtMost (Over.mk p) 1)
local notation "x" => t ≫ pullback.fst f f
local notation "y" => t ≫ pullback.snd f f
include e ht

/-- The actual comparison projection equalizes both full coefficient endpoints. -/
theorem originalBoundary_rankOne_equalizer_condition :
    pullback.snd c t ≫ x = pullback.snd c t ≫ y := by
  have hr : Set.range ((pullback.snd c t ≫ t) ≫ pullback.fst f f ≫ J.subschemeι) ⊆
      rankAtMost (Over.mk p) 1 := by
    rintro _ ⟨z, rfl⟩
    exact ht ⟨pullback.snd c t z, rfl⟩
  let _ := originalBoundaryComparison_mono e J hJ
  have hd : ∃! d : pullback c t ⟶ pullback p J.subschemeι,
      d ≫ c = pullback.snd c t ≫ t :=
    ⟨pullback.fst c t, pullback.condition, fun d hd ↦
      (cancel_mono c).mp (hd.trans pullback.condition.symm)⟩
  simpa only [Category.assoc] using
    (originalBoundary_rankOne_comparison_lift_iff J e hJ _ hr).mp hd

/-- The full original comparison maps canonically to the exact endpoint equalizer. -/
def originalBoundaryRankOneToEqualizer : pullback c t ⟶ equalizer x y :=
  equalizer.lift (pullback.snd c t) (originalBoundary_rankOne_equalizer_condition J e hJ t ht)

/-- The comparison-to-equalizer map keeps the entire coefficient morphism. -/
@[reassoc] theorem originalBoundaryRankOneToEqualizer_ι :
    originalBoundaryRankOneToEqualizer J e hJ t ht ≫ equalizer.ι x y = pullback.snd c t :=
  equalizer.lift_ι _ _

/-- The equalizer supplies an actual original arrow over its full nonreduced scheme. -/
theorem originalBoundary_rankOne_equalizer_arrow :
    ∃ d : equalizer x y ⟶ pullback p J.subschemeι,
      d ≫ c = equalizer.ι x y ≫ t := by
  have hr : Set.range ((equalizer.ι x y ≫ t) ≫ pullback.fst f f ≫ J.subschemeι) ⊆
      rankAtMost (Over.mk p) 1 := by
    rintro _ ⟨z, rfl⟩
    exact ht ⟨equalizer.ι x y z, rfl⟩
  apply ((originalBoundary_rankOne_comparison_lift_iff J e hJ _ hr).mpr ?_).exists
  simpa only [Category.assoc] using equalizer.condition x y

/-- The constructed original arrow returns the equalizer to the actual comparison pullback. -/
def originalBoundaryRankOneFromEqualizer : equalizer x y ⟶ pullback c t :=
  pullback.lift (originalBoundary_rankOne_equalizer_arrow J e hJ t ht).choose
    (equalizer.ι x y) (originalBoundary_rankOne_equalizer_arrow J e hJ t ht).choose_spec

/-- The return map keeps exactly the same original coefficient. -/
@[reassoc] theorem originalBoundaryRankOneFromEqualizer_snd :
    originalBoundaryRankOneFromEqualizer J e hJ t ht ≫ pullback.snd c t = equalizer.ι x y :=
  pullback.lift_snd _ _ _

attribute [local irreducible] originalBoundaryRankOneToEqualizer
  originalBoundaryRankOneFromEqualizer

/-- The full rank-one comparison is the full scheme-theoretic endpoint equalizer. -/
def originalBoundaryRankOneEqualizerIso : pullback c t ≅ equalizer x y := by
  let _ := originalBoundaryComparison_mono e J hJ
  exact rankOneEqualizerIsoOfMonoProjections (pullback.snd c t) (equalizer.ι x y)
    (originalBoundaryRankOneToEqualizer J e hJ t ht)
    (originalBoundaryRankOneFromEqualizer J e hJ t ht)
    (originalBoundaryRankOneToEqualizer_ι J e hJ t ht)
    (originalBoundaryRankOneFromEqualizer_snd J e hJ t ht)

/-- The isomorphism is over the unchanged coefficient test. -/
@[reassoc] theorem originalBoundaryRankOneEqualizerIso_ι :
    (originalBoundaryRankOneEqualizerIso J e hJ t ht).hom ≫ equalizer.ι x y =
      pullback.snd c t := originalBoundaryRankOneToEqualizer_ι J e hJ t ht

/-- The exact original comparison ideal is the exact endpoint equalizer ideal. -/
theorem originalBoundary_rankOne_comparison_kernel :
    (pullback.snd c t).ker = (equalizer.ι x y).ker := by
  rw [← originalBoundaryRankOneEqualizerIso_ι J e hJ t ht, Scheme.Hom.ker_comp_of_isIso]

end FLT.Mazur.EquivalenceRelationOrderedFrames
