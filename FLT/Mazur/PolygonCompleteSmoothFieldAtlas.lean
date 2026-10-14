/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldMarkedSubgroup
public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientSubgroup
public import FLT.Mazur.CyclicCharacteristicAtlasModuli

/-!
# Original smooth field squares in the full cyclic atlas

The actual original complete divisor gives an ample cyclic modular class.
Both characteristic charts cover that class by full compatible subgroup
isomorphisms. The class commutes with the specified coefficient extensions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "S" => Spec (CommRingCat.of L)
local notation "E" => completeFieldGeneralizedCurve K n h L a ha p q hs (0 : Fin n)
local notation "H" => completeFieldFiniteSubgroup K n h L a ha p q hs

/-- The actual original smooth field curve and product divisor define an ample cyclic class. -/
def completeFieldModuliClass : ampleCyclicClasses S n :=
  Quotient.mk _ ⟨⟨E, H⟩, completeFieldFiniteSubgroup_isCyclic K n h L a ha p q hs,
    completeFieldFiniteSubgroup_isAmple K n h L a ha p q hs⟩

/-- Both characteristic charts cover the original divisor with full DR/subgroup comparisons. -/
theorem completeField_exists_atlas_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (d : C.I₀ → Bool)
      (v : ∀ i : C.I₀, C.X i ⟶ CyclicCharacteristicAtlas.locus n (d i)),
      ∀ i, Nonempty (CompatibleIso
        ((CyclicCharacteristicAtlas.subgroup n (d i)).baseChange (v i))
        ((H).baseChange (C.f i))) := by
  let _ : SmoothOfRelativeDimension 1 (E).curve.hom :=
    completeCartesianField_relativeDimension K n h L a ha p q hs
  let _ : Smooth (E).curve.hom := SmoothOfRelativeDimension.smooth 1 _
  exact CyclicCharacteristicAtlas.exists_original_fppf_cover_unrestricted H
    (completeFieldFiniteSubgroup_isCyclic K n h L a ha p q hs)

/-- The same cover identifies the actual original modular class on every chart. -/
theorem completeField_exists_moduli_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (d : C.I₀ → Bool)
      (v : ∀ i : C.I₀, C.X i ⟶ CyclicCharacteristicAtlas.locus n (d i)),
      ∀ i, ampleCyclicClassesPullback (v i) n (CyclicCharacteristicAtlas.moduliClass n (d i)) =
        ampleCyclicClassesPullback (C.f i) n (completeFieldModuliClass K n h L a ha p q hs) := by
  obtain ⟨C, d, v, hv⟩ := completeField_exists_atlas_cover K n h L a ha p q hs
  exact ⟨C, d, v, fun i ↦ Quotient.sound (hv i)⟩

variable (M : Type) [Field M] [Algebra L M]
  {Z : Scheme} (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of M))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap L M).comp a))))

/-- The actual original modular class commutes with the specified coefficient extension. -/
theorem completeFieldModuliClass_coefficient :
    ampleCyclicClassesPullback (Spec.map (CommRingCat.ofHom (algebraMap L M))) n
      (completeFieldModuliClass K n h L a ha p q hs) =
        completeFieldModuliClass K n h M ((algebraMap L M).comp a)
          ((map_ne_zero (algebraMap L M)).mpr ha) r s ht :=
  Quotient.sound ⟨completeFieldCoefficientSubgroupIso K n h L a ha p q hs M r s ht⟩

end FLT.Mazur.PolygonInfinitesimalStages
