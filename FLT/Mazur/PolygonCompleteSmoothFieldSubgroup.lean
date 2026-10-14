/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldCyclic
public import FLT.Mazur.PolygonCompleteSmoothFieldGroupHom
public import FLT.Mazur.PolygonCompleteCyclicDivisor
public import FLT.Mazur.GeneralizedCurveAmpleSubgroup
public import FLT.Mazur.GeneralizedCurveFiberAmple

/-!
# The original complete divisor on its full smooth field curve

The carrier is the actual pulled-back complete product ideal. Its inclusion is
a homomorphism into the constructed full group, its original generator is
Cartier, and its positive rank gives ampleness on the smooth integral curve.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "S" => Spec (CommRingCat.of L)
local notation "E" => completeFieldGeneralizedCurve K n h L a ha p q hs (0 : Fin n)

/-- The original complete divisor included into the entire smooth field group. -/
def completeFieldDivisorInclusion : completeCyclicDivisor K n h p q ⟶ Over.mk q :=
  (completeCyclicDivisorIso K n h s p q hs).inv ≫ completeCyclicMarking K n h s p q hs

/-- The full group inclusion retains the exact original closed subscheme map. -/
theorem completeFieldDivisorInclusion_left :
    (completeFieldDivisorInclusion K n h L a p q hs).left =
      ((completeMarkingDivisor K n h).comap p).subschemeι := by
  apply (cancel_epi (completeCyclicDivisorSchemeIso K n h s p q hs).hom).mp
  change (completeCyclicDivisorSchemeIso K n h s p q hs).hom ≫
    (completeCyclicDivisorSchemeIso K n h s p q hs).inv ≫
      (completeCyclicMarking K n h s p q hs).left = _
  rw [Iso.hom_inv_id_assoc, completeCyclicDivisorSchemeIso_ι]

/-- The actual original product divisor is a finite subgroup of the full smooth field curve. -/
def completeFieldFiniteSubgroup : (E).FiniteSubgroup n := by
  let _ := completeCyclicDivisorCommGrpObj K n h s p q hs
  let _ := completeFieldCommGrp K n h L a ha p q hs (0 : Fin n)
  let _ := completeCyclicMarking_field_isMonHom K n h L a ha p q hs
  refine
    { carrier := completeCyclicDivisor K n h p q
      inclusion := completeFieldDivisorInclusion K n h L a p q hs
      isMonHom := ?_
      closed := ?_
      degree := completeCyclicDivisor_degree K n h s p q hs }
  · dsimp only [completeFieldDivisorInclusion]
    infer_instance
  · rw [completeFieldDivisorInclusion_left]
    infer_instance

/-- The subgroup's map into the curve is the unchanged original product-divisor embedding. -/
@[simp] theorem completeFieldFiniteSubgroup_curveMap :
    (completeFieldFiniteSubgroup K n h L a ha p q hs).curveMap.left =
      ((completeMarkingDivisor K n h).comap p).subschemeι := by
  rw [FiniteSubgroup.curveMap, completeFieldGeneralizedCurve_inclusion, Category.comp_id]
  exact completeFieldDivisorInclusion_left K n h L a p q hs

/-- The original complete ideal is retained scheme-theoretically. -/
@[simp] theorem completeFieldFiniteSubgroup_ideal :
    (completeFieldFiniteSubgroup K n h L a ha p q hs).ideal =
      (completeMarkingDivisor K n h).comap p := by
  rw [FiniteSubgroup.ideal, completeFieldFiniteSubgroup_curveMap,
    Scheme.IdealSheafData.ker_subschemeι]

/-- The original complete relative Cartier divisor remains Cartier on this specified square. -/
theorem completeFieldFiniteSubgroup_relativeCartier :
    FCurve.RelativeEffectiveCartier q (completeFieldFiniteSubgroup K n h L a ha p q hs).ideal := by
  rw [completeFieldFiniteSubgroup_ideal]
  exact FCurve.relativeCartier_originalSquare hs _ (completeMarkingDivisor_relativeCartier K n h)

/-- The original finite divisor generator over the unchanged field. -/
def completeFieldGenerator :
    𝟙_ (Over S) ⟶ (completeFieldFiniteSubgroup K n h L a ha p q hs).carrier :=
  ConstantCyclicGroup.component S n 1 ≫ (completeCyclicDivisorIso K n h s p q hs).hom

/-- Its powers give precisely the original complete marked sections. -/
theorem completeFieldGenerator_orbit (i : Fin n) :
    ((completeFieldGenerator K n h L a ha p q hs ^ i.val) ≫
        (completeFieldFiniteSubgroup K n h L a ha p q hs).curveMap).left =
      completeCartesianMarking K n h s p q hs i := by
  let _ := completeCyclicDivisorCommGrpObj K n h s p q hs
  have : IsMonHom (completeCyclicDivisorIso K n h s p q hs).hom := by infer_instance
  rw [completeFieldGenerator, ← MonObj.pow_comp, Over.comp_left,
    completeFieldFiniteSubgroup_curveMap, Over.comp_left, Category.assoc]
  rw [show (completeCyclicDivisorIso K n h s p q hs).hom.left =
      (completeCyclicDivisorSchemeIso K n h s p q hs).hom from rfl,
    completeCyclicDivisorSchemeIso_ι, ← ConstantCyclicGenerator.component_pow]
  change ((ConstantCyclicGroup.component S n (ZMod.finEquiv n i)) ≫
    completeCyclicMarking K n h s p q hs).left = _
  rw [completeCyclicMarking_component]
  simp only [completeCyclicSection, Over.homMk_left, RingEquiv.symm_apply_apply]

/-- The scheme-theoretic sum of powers equals the original complete product ideal. -/
theorem completeFieldGenerator_isCartierGenerator :
    (completeFieldFiniteSubgroup K n h L a ha p q hs).IsCartierGenerator
      (completeFieldGenerator K n h L a ha p q hs) := by
  let _ := completeCyclicDivisorCommGrpObj K n h s p q hs
  have : IsMonHom (completeCyclicDivisorIso K n h s p q hs).hom := by infer_instance
  refine ⟨?_, completeFieldFiniteSubgroup_relativeCartier K n h L a ha p q hs, ?_⟩
  · rw [completeFieldGenerator, ← MonObj.pow_comp, ← ConstantCyclicGenerator.component_natCast,
      ZMod.natCast_self, ConstantCyclicGenerator.component_zero, MonObj.one_comp]
  · simp only [completeFieldFiniteSubgroup_ideal, completeMarkingDivisor,
      FCurve.idealSheaf_comap_prod, completeCartesianMarking_ker K n h s p q hs,
      completeFieldGenerator_orbit]

/-- The actual finite subgroup is fppf cyclic. -/
theorem completeFieldFiniteSubgroup_isCyclic :
    (completeFieldFiniteSubgroup K n h L a ha p q hs).IsCyclic :=
  (completeFieldGenerator_isCartierGenerator K n h L a ha p q hs).isCyclic _

/-- The original positive-rank subgroup divisor is ample on the original smooth field curve. -/
theorem completeFieldFiniteSubgroup_isAmple :
    (completeFieldFiniteSubgroup K n h L a ha p q hs).IsAmple := by
  let H := completeFieldFiniteSubgroup K n h L a ha p q hs
  let _ := completeCartesianField_relativeDimension K n h L a ha p q hs
  let _ := completeField_geometricallyIntegral K n h L a ha p q hs
  let _ := (completeField_classifiedGenusOneFamily K n h L a p q hs).family.1
  let _ : IsFinite
      ((completeFieldFiniteSubgroup K n h L a ha p q hs).ideal.subschemeι ≫ q) :=
    H.ideal_degree.1
  let hI := (completeFieldFiniteSubgroup_relativeCartier K n h L a ha p q hs).1
  refine ⟨hI, (FCurve.smooth_divisor_relativeAmple_iff_nonempty q hI).mpr ?_⟩
  rw [FiniteSubgroup.ideal, Scheme.Hom.support_ker]
  let x : S := ⟨⊥, inferInstance⟩
  exact ⟨_, subset_closure ⟨(completeFieldGenerator K n h L a ha p q hs).left x, rfl⟩⟩

end FLT.Mazur.PolygonInfinitesimalStages
