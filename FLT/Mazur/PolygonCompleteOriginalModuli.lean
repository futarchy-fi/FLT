/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteOriginalCyclicSubgroup
public import FLT.Mazur.CyclicCharacteristicNormalizedModuli

/-!
# The complete boundary family maps to the original modular presheaf

The full generalized curve and its original ample cyclic divisor give a
natural modular class on every base change. On every smooth base change,
the two normalized characteristic charts cover this same original class.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "B" => Spec (CommRingCat.of (PowerSeries K))
local notation "E" => completeGeneralizedCurve K n h
local notation "H" => completeOriginalFiniteSubgroup K n h

/-- The original complete family and product divisor define an ample cyclic modular class. -/
def completeOriginalModuliClass : ampleCyclicClasses B n :=
  Quotient.mk _ ⟨⟨E, H⟩, completeOriginalFiniteSubgroup_isCyclic K n h,
    completeOriginalFiniteSubgroup_isAmple K n h⟩

/-- The actual complete boundary parameter maps naturally to the modular presheaf. -/
def completeOriginalModuliMap :
    yoneda.obj B ⋙ uliftFunctor.{1} ⟶ ampleCyclicClassPresheaf n where
  app T := ↾(fun p ↦ ampleCyclicClassesPullback p.down n (completeOriginalModuliClass K n h))
  naturality T U g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact congrFun (ampleCyclicClassesPullback_comp p.down g.unop n)
      (completeOriginalModuliClass K n h)

/-- The two normalized smooth charts cover each smooth base change of the boundary family. -/
theorem completeOriginal_exists_normalized_cover {T : Scheme} (g : T ⟶ B)
    [Smooth ((E).baseChange g).curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage T) (d : C.I₀ → Bool)
      (v : ∀ i : C.I₀, C.X i ⟶ CyclicCharacteristicAtlas.normalizedLocus n (d i)),
      ∀ i, (CyclicCharacteristicAtlas.normalizedModuliMap n (d i)).app
        (Opposite.op (C.X i)) (ULift.up (v i)) =
          (completeOriginalModuliMap K n h).app (Opposite.op (C.X i))
            (ULift.up (C.f i ≫ g)) := by
  obtain ⟨C, d, v, hv⟩ := CyclicCharacteristicAtlas.exists_normalized_moduli_fppf_cover n
    ((H).baseChange g) ((completeOriginalFiniteSubgroup_isCyclic K n h).baseChange (H) g)
    ((completeOriginalFiniteSubgroup_isAmple K n h).baseChange g)
  refine ⟨C, d, v, fun i ↦ ?_⟩
  rw [hv i]
  exact (congrFun (ampleCyclicClassesPullback_comp g (C.f i) n)
    (completeOriginalModuliClass K n h)).symm

/-- Every nonzero-parameter field fiber is covered by the actual normalized smooth charts. -/
theorem completeOriginalField_exists_normalized_cover (L : Type) [Field L]
    (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0) :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of L))) (d : C.I₀ → Bool)
      (v : ∀ i : C.I₀, C.X i ⟶ CyclicCharacteristicAtlas.normalizedLocus n (d i)),
      ∀ i, (CyclicCharacteristicAtlas.normalizedModuliMap n (d i)).app
        (Opposite.op (C.X i)) (ULift.up (v i)) =
          (completeOriginalModuliMap K n h).app (Opposite.op (C.X i))
            (ULift.up (C.f i ≫ Spec.map (CommRingCat.ofHom a))) := by
  let g := Spec.map (CommRingCat.ofHom a)
  let _ := completeCartesianField_relativeDimension K n h L a ha
    (Limits.pullback.fst (E).curve.hom g) (Limits.pullback.snd (E).curve.hom g)
    (IsPullback.of_hasPullback _ _)
  let _ : Smooth ((E).baseChange g).curve.hom := by
    change Smooth (Limits.pullback.snd (E).curve.hom g)
    exact SmoothOfRelativeDimension.smooth 1 _
  exact completeOriginal_exists_normalized_cover K n h g

/-- Every common relabeling retains the comparison with that same boundary-family class. -/
theorem completeOriginal_normalized_relabel {T : Scheme} (g : T ⟶ B) (d : Bool)
    (v : T ⟶ CyclicCharacteristicAtlas.normalizedLocus n d)
    (hv : (CyclicCharacteristicAtlas.normalizedModuliMap n d).app (Opposite.op T)
      (ULift.up v) = (completeOriginalModuliMap K n h).app (Opposite.op T) (ULift.up g))
    (e : CyclicCharacteristicAtlas.RelabelGroup n) :
    (CyclicCharacteristicAtlas.normalizedModuliMap n d).app (Opposite.op T)
      (ULift.up (v ≫ (CyclicCharacteristicAtlas.normalizedRelabelAction n d e).hom)) =
        (completeOriginalModuliMap K n h).app (Opposite.op T) (ULift.up g) :=
  (CyclicCharacteristicAtlas.normalizedModuliMap_action n d v e).trans hv

end FLT.Mazur.PolygonInfinitesimalStages
