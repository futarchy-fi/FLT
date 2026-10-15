/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticFamilyHomExt

/-!
# Algebraizing original-stage factorizations through a closed target

Pull back the target's closed immersion. Every original arithmetic stage
factors through that pullback, so its kernel lies in every parameter power.
Full ideal separation makes the pullback an isomorphism. This retains the
specified target map at each order, without assuming a global factorization.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj family exactVeroneseProj
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Stage factorizations force a closed target pullback to be the entire arithmetic source. -/
theorem completeClosedTarget_pullback_isIso {Y Z : Scheme} (i : Z ⟶ Y)
    [IsClosedImmersion i] (f : exactVeroneseProj A π n h hne hgen ⟶ Y)
    (g : ∀ m, (family A π m n h).left ⟶ Z)
    (hg : ∀ m, g m ≫ i = originalStageToCompatibleProj A π hne hgen n h m ≫ f) :
    IsIso (pullback.fst f i) := by
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  apply completeIdeal_eq_bot_of_le_powers A π hne hgen n h
  intro m
  have hm := (pullback.lift (originalStageToCompatibleProj A π hne hgen n h m)
    (g m) (hg m).symm).le_ker_comp (pullback.fst f i)
  rw [pullback.lift_fst, ← originalStageAdicIso_hom_ι,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι] at hm
  exact hm

/-- Original stage maps into a closed target reconstruct uniquely from an ambient morphism. -/
theorem completeClosedTarget_existsUnique {Y Z : Scheme} (i : Z ⟶ Y)
    [IsClosedImmersion i] (f : exactVeroneseProj A π n h hne hgen ⟶ Y)
    (g : ∀ m, (family A π m n h).left ⟶ Z)
    (hg : ∀ m, g m ≫ i = originalStageToCompatibleProj A π hne hgen n h m ≫ f) :
    ∃! k : exactVeroneseProj A π n h hne hgen ⟶ Z,
      k ≫ i = f ∧ ∀ m, originalStageToCompatibleProj A π hne hgen n h m ≫ k = g m := by
  let _ := completeClosedTarget_pullback_isIso A π hne hgen n h i f g hg
  let k := inv (pullback.fst f i) ≫ pullback.snd f i
  have hk : k ≫ i = f := by
    dsimp only [k]
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  refine ⟨k, ⟨hk, ?_⟩, ?_⟩
  · intro m
    apply (cancel_mono i).mp
    rw [Category.assoc, hk, hg m]
  · intro k' hk'
    exact (cancel_mono i).mp (hk'.1.trans hk.symm)

end FLT.Mazur.PolygonArithmeticStages
