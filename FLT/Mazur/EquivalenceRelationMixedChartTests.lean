/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedChartProjections

/-!
# Testing full mixed chart equations on arbitrary schemes

Every original arrow between chart-valued tests factors through the entire
mixed chart relation. The reflexive case gives the actual overlap equations
needed for descent of regular functions, including nonreduced tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
variable {T : Scheme.{0}} (u : T ⟶ U.toScheme) (v : T ⟶ V.toScheme)
  (a : T ⟶ D)
  (ha : a ≫ p = u ≫ U.ι ≫ first p q I o)
  (hb : a ≫ q = v ≫ V.ι ≫ first p q J o')
set_option quotPrecheck false
local notation "l" => lift p q I J o o' (u ≫ U.ι) (v ≫ V.ι) a
  (ha.trans (Category.assoc _ _ _).symm) (hb.trans (Category.assoc _ _ _).symm)

/-- The lifted original arrow lands in both prescribed chart opens. -/
theorem lift_range_mixedChart : Set.range l ⊆ Set.range (mixedChartOpen o o' U V).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  change fst p q I J o o' (l x) ∈ U ∧ snd p q I J o o' (l x) ∈ V
  have hf := congrArg (fun g ↦ g x) (lift_fst p q I J o o' (u ≫ U.ι) (v ≫ V.ι) a
    (ha.trans (Category.assoc _ _ _).symm) (hb.trans (Category.assoc _ _ _).symm))
  have hg := congrArg (fun g ↦ g x) (lift_snd p q I J o o' (u ≫ U.ι) (v ≫ V.ι) a
    (ha.trans (Category.assoc _ _ _).symm) (hb.trans (Category.assoc _ _ _).symm))
  exact ⟨hf.symm ▸ (u x).property, hg.symm ▸ (v x).property⟩

/-- The actual scheme map to the full mixed chart relation. -/
def mixedChartLift : T ⟶ (mixedChartOpen o o' U V).toScheme :=
  IsOpenImmersion.lift _ l (lift_range_mixedChart o o' U V u v a ha hb)

/-- Factoring through the open retains the entire original arrow. -/
@[reassoc] theorem mixedChartLift_inclusion :
    mixedChartLift o o' U V u v a ha hb ≫ (mixedChartOpen o o' U V).ι = l :=
  IsOpenImmersion.lift_fac _ l (lift_range_mixedChart o o' U V u v a ha hb)

/-- The first chart-valued test is unchanged by the factorization. -/
@[reassoc] theorem mixedChartLift_first :
    mixedChartLift o o' U V u v a ha hb ≫ mixedChartFirst o o' U V = u := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, mixedChartFirst, Scheme.Hom.resLE_comp_ι,
    mixedChartLift_inclusion_assoc, lift_fst]

/-- The second chart-valued test is unchanged by the factorization. -/
@[reassoc] theorem mixedChartLift_second :
    mixedChartLift o o' U V u v a ha hb ≫ mixedChartSecond o o' U V = v := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, mixedChartSecond, Scheme.Hom.resLE_comp_ι,
    mixedChartLift_inclusion_assoc, lift_snd]

include a ha hb in
/-- Full mixed compatibility implies equality on every original-arrow test. -/
theorem mixedChart_compatible_test (s : Γ(U.toScheme, ⊤)) (t : Γ(V.toScheme, ⊤))
    (h : (mixedChartFirst o o' U V).appTop s = (mixedChartSecond o o' U V).appTop t) :
    u.appTop s = v.appTop t := by
  have he := congrArg (fun z ↦ (mixedChartLift o o' U V u v a ha hb).appTop z) h
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    mixedChartLift_first, mixedChartLift_second] using he

variable (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- The full relation equations imply descent compatibility whenever original endpoints agree. -/
theorem mixedChart_compatible_same_endpoint
    (huv : u ≫ U.ι ≫ first p q I o = v ≫ V.ι ≫ first p q J o')
    (s : Γ(U.toScheme, ⊤)) (t : Γ(V.toScheme, ⊤))
    (h : (mixedChartFirst o o' U V).appTop s = (mixedChartSecond o o' U V).appTop t) :
    u.appTop s = v.appTop t := by
  apply mixedChart_compatible_test o o' U V u v
    (u ≫ U.ι ≫ first p q I o ≫ e.r) _ _ s t h
  · simp only [Category.assoc, e.reflexivity₁, Category.comp_id]
  · simpa only [Category.assoc, e.reflexivity₂, Category.comp_id] using huv

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
