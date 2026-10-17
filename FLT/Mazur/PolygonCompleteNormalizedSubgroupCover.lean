/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicNormalizedSubgroup
public import FLT.Mazur.PolygonCompleteOriginalModuli

/-!
# Normalized charts retain the actual complete-family subgroup

On each smooth base change the normalized characteristic charts cover by full
compatible subgroup comparisons. The comparison targets the direct complete
pullback, and transports its original Cartier generator to the chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "B" => Spec (CommRingCat.of (PowerSeries K))
local notation "E" => completeGeneralizedCurve K n h
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "P" => completeOriginalGenerator K n h

/-- The actual normalized subgroups compare with the direct complete-family pullbacks. -/
theorem completeOriginal_exists_normalized_subgroup_cover {T : Scheme} (g : T ⟶ B)
    [Smooth ((E).baseChange g).curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage T) (d : C.I₀ → Bool)
      (v : ∀ i : C.I₀, C.X i ⟶ CyclicCharacteristicAtlas.normalizedLocus n (d i)),
      ∀ i, Nonempty (CompatibleIso
        ((CyclicCharacteristicAtlas.normalizedSubgroup n (d i)).baseChange (v i))
        ((H).baseChange (C.f i ≫ g))) := by
  obtain ⟨C, d, v, hv⟩ :=
    CyclicCharacteristicAtlas.exists_normalized_subgroup_fppf_cover n ((H).baseChange g)
      ((completeOriginalFiniteSubgroup_isCyclic K n h).baseChange (H) g)
      ((completeOriginalFiniteSubgroup_isAmple K n h).baseChange g)
  refine ⟨C, d, v, fun i ↦ ?_⟩
  obtain ⟨e⟩ := hv i
  exact ⟨e.trans (compatibleBaseChangeComp (H) g (C.f i)).symm⟩

/-- Every such actual comparison gives a Cartier generator on the normalized chart. -/
theorem completeOriginal_normalized_chart_generator {T : Scheme} (g : T ⟶ B) (d : Bool)
    (v : T ⟶ CyclicCharacteristicAtlas.normalizedLocus n d)
    (e : CompatibleIso ((CyclicCharacteristicAtlas.normalizedSubgroup n d).baseChange v)
      ((H).baseChange g)) :
    ((CyclicCharacteristicAtlas.normalizedSubgroup n d).baseChange v).IsCartierGenerator
      (pullSection g (P) ≫ e.subgroup.inv) :=
  e.symm.cartierGenerator ((completeOriginalGenerator_isCartierGenerator K n h).baseChange (H) g)

/-- All powers of the chart generator are the actual original complete generator sections. -/
theorem completeOriginal_normalized_chart_generator_pow {T : Scheme} (g : T ⟶ B) (d : Bool)
    (v : T ⟶ CyclicCharacteristicAtlas.normalizedLocus n d)
    (e : CompatibleIso ((CyclicCharacteristicAtlas.normalizedSubgroup n d).baseChange v)
      ((H).baseChange g)) (m : ℕ) :
    ((pullSection g (P) ≫ e.subgroup.inv) ^ m) ≫ e.subgroup.hom =
      pullSection g ((P) ^ m) := by
  rw [MonObj.pow_comp, Category.assoc, e.subgroup.inv_hom_id]
  change ((pullSection g (P) ≫ 𝟙 _) ^ m) = _
  rw [Category.comp_id, section_pow]

/-- Common relabelings retain the original full complete-family subgroup on each chart. -/
theorem completeOriginal_normalized_relabel_subgroup {T : Scheme} (g : T ⟶ B) (d : Bool)
    (v : T ⟶ CyclicCharacteristicAtlas.normalizedLocus n d)
    (e : CompatibleIso ((CyclicCharacteristicAtlas.normalizedSubgroup n d).baseChange v)
      ((H).baseChange g)) (a : CyclicCharacteristicAtlas.RelabelGroup n) :
    Nonempty (CompatibleIso ((CyclicCharacteristicAtlas.normalizedSubgroup n d).baseChange
      (v ≫ (CyclicCharacteristicAtlas.normalizedRelabelAction n d a).hom))
        ((H).baseChange g)) := by
  obtain ⟨r⟩ := CyclicCharacteristicAtlas.normalizedRelabel_subgroup n d v a
  exact ⟨r.trans e⟩

end FLT.Mazur.PolygonInfinitesimalStages
