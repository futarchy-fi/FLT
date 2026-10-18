/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFaithfulCyclicLine
public import FLT.Mazur.OneGonSmoothingMarkingAmple

/-!
# Ampleness of the entire lifted cyclic subgroup divisor

Every field fiber of the original complete cubic is integral. Its actual
finite cyclic Cartier divisor has nonempty support, hence is ample. Properness
over the local coefficient ring then gives ampleness on the original family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "f" => Over.hom (family (PowerSeries.X : PowerSeries K))
local notation "I" => faithfulCompleteIdeal K n labels hlabels
local notation "L" => faithfulCompleteCyclicLine K n labels hlabels

/-- The original full cyclic divisor line is ample on every actual field fiber. -/
theorem faithfulCompleteCyclicLine_field_ample (F : Type) [Field F]
    (s : Spec (.of F) ⟶ Spec (.of (PowerSeries K))) :
    AmpleLineBundle ((Scheme.Modules.pullback (pullback.fst (f) s)).obj (L)) := by
  let _ := family_proper (t)
  let _ := integralCurveFieldSquare_isIntegral (equation (t)) s _ (pullback.snd (f) s)
    (IsPullback.of_hasPullback _ _)
  let _ := faithfulCompleteIdeal_baseChange_finite K n labels hlabels s
  have hc := completeCartesian_classified K F s _ (pullback.snd (f) s)
    (IsPullback.of_hasPullback _ _)
  have ha : AmpleLineBundle (divisorLineBundle ((I).comap (pullback.fst (f) s))
      (faithfulCompleteIdeal_baseChange_cartier K n labels hlabels s).1) := by
    apply (divisor_ample_iff_meets_components (pullback.snd (f) s)
      (faithfulCompleteIdeal_baseChange_cartier K n labels hlabels s).1 hc.pureDimension).mpr
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst Z
    rw [Set.inter_univ]
    exact faithfulCompleteIdeal_baseChange_nonempty K n labels hlabels s
  exact ha.of_iso (faithfulCompleteCyclicLineBaseChangeIso K n labels hlabels s)

/-- The actual whole-subgroup line is ample on the original complete cubic. -/
theorem faithfulCompleteCyclicLine_ample : AmpleLineBundle (L) := by
  let x := IsLocalRing.closedPoint (PowerSeries K)
  let _ := family_proper (t)
  have ha : AmpleLineBundle ((Scheme.Modules.pullback ((f).fiberι x)).obj (L)) :=
    faithfulCompleteCyclicLine_field_ample K n labels hlabels _
      ((Spec (.of (PowerSeries K))).fromSpecResidueField x)
  obtain ⟨U, hU, _, hA⟩ := exists_ample_neighborhood_spectrum_proper (f) x _
    (faithfulCompleteCyclicLine_rankOne K n labels hlabels) ha
  have htop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hU
  rw [htop, Scheme.Hom.preimage_top] at hA
  let _ : IsIso (⊤ : (family (t)).left.Opens).ι :=
    (family (t)).left.topIso.isIso_hom
  exact (ampleLineBundle_pullback_iso_iff _ _).mp hA

/-- The full constructed subgroup is relatively ample over the unchanged complete base. -/
theorem faithfulCompleteCyclicLine_relativelyAmple : RelativelyAmpleLineBundle (f) (L) := by
  let _ := family_proper (t)
  exact (faithfulCompleteCyclicLine_ample K n labels hlabels).relative_of_affine _

/-- The actual pulled-back cyclic divisor line remains relatively ample on every test base. -/
theorem faithfulCompleteCyclicLine_baseChange_relativelyAmple {T : Scheme}
    (g : T ⟶ Spec (.of (PowerSeries K))) :
    RelativelyAmpleLineBundle (pullback.snd (f) g)
      (divisorLineBundle ((I).comap (pullback.fst (f) g))
        (faithfulCompleteIdeal_baseChange_cartier K n labels hlabels g).1) := by
  let _ := family_proper (t)
  exact ((faithfulCompleteCyclicLine_relativelyAmple K n labels hlabels).baseChange g).of_iso
    (faithfulCompleteCyclicLineBaseChangeIso K n labels hlabels g).symm

end FLT.Mazur.OneGonSmoothing
