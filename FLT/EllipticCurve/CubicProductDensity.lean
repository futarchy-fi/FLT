/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicGlobalIdentity

/-! # Determination of product morphisms by the ordinary charts -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

@[reassoc] theorem sourceChart_baseChangeIso
    (S : Type u) [CommRing S] [Algebra R S] (b : Bool) :
    sourceChart (W.map (algebraMap R S)) b ≫ (baseChangeIso W S).hom =
      (chartBaseChange_isPullback W S b).isoPullback.hom ≫
        chartBaseChangeInclusion W
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) b := by
  apply pullback.hom_ext
  · simp [chartBaseChangeInclusion, pullback.map, Category.assoc,
      chartCoefficientMorphism]
  · simp [chartBaseChangeInclusion, pullback.map, Category.assoc]

/-- After any coefficient extension, the ordinary first chart still determines a morphism
from the base-changed cubic to a separated relative target. -/
theorem baseChanged_affineChart_hom_ext
    (S : Type u) [CommRing S] [Algebra R S]
    {Y B : Scheme.{u}} (s : Y ⟶ B) [IsSeparated s]
    {f g : pullback (toBase W)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⟶ Y}
    (hbase : f ≫ s = g ≫ s)
    (h : chartBaseChangeInclusion W
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) false ≫ f =
      chartBaseChangeInclusion W
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) false ≫ g) : f = g := by
  apply (cancel_epi (baseChangeIso W S).hom).mp
  apply affineChart_hom_ext (W.map (algebraMap R S)) s
  · simpa only [Category.assoc] using congrArg (fun k ↦ (baseChangeIso W S).hom ≫ k) hbase
  · change sourceChart (W.map (algebraMap R S)) false ≫ ((baseChangeIso W S).hom ≫ f) =
      sourceChart (W.map (algebraMap R S)) false ≫ ((baseChangeIso W S).hom ≫ g)
    rw [sourceChart_baseChangeIso_assoc, sourceChart_baseChangeIso_assoc, h]

@[reassoc] theorem chartBaseChangeInclusion_symmetry
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (b : Bool) :
    chartBaseChangeInclusion W f b ≫ (pullbackSymmetry (toBase W) f).hom =
      (pullbackSymmetry (chartToBase W b) f).hom ≫ chartRightBaseChangeInclusion W f b := by
  apply pullback.hom_ext <;>
    simp [chartBaseChangeInclusion, chartRightBaseChangeInclusion, pullback.map, Category.assoc]

@[reassoc] theorem chartPairInclusion_factor_right (b c : Bool) :
    chartPairInclusion W b c =
      chartRightBaseChangeInclusion W (chartToBase W b) c ≫
        chartBaseChangeInclusion W (toBase W) b := by
  apply pullback.hom_ext <;>
    simp [chartPairInclusion, chartBaseChangeInclusion, chartRightBaseChangeInclusion,
      pullback.map, Category.assoc]

@[reassoc] theorem chartPairInclusion_symmetry (b c : Bool) :
    chartPairInclusion W b c ≫ (pullbackSymmetry (toBase W) (toBase W)).hom =
      (pullbackSymmetry (chartToBase W b) (chartToBase W c)).hom ≫
        chartPairInclusion W c b := by
  apply pullback.hom_ext <;>
    simp [chartPairInclusion, pullback.map, Category.assoc]

/-- A morphism from the full cubic product to a separated relative target is determined
by its restriction to the ordinary-affine product, even over a nonreduced base. -/
theorem affinePair_hom_ext {Y B : Scheme.{u}} (s : Y ⟶ B) [IsSeparated s]
    {f g : pullback (toBase W) (toBase W) ⟶ Y} (hbase : f ≫ s = g ≫ s)
    (h : chartPairInclusion W false false ≫ f = chartPairInclusion W false false ≫ g) :
    f = g := by
  have ha : chartBaseChangeInclusion W (toBase W) false ≫ f =
      chartBaseChangeInclusion W (toBase W) false ≫ g := by
    apply (cancel_epi (pullbackSymmetry (toBase W) (chartToBase W false)).hom).mp
    apply baseChanged_affineChart_hom_ext W (Ring W false) s
    · simpa only [Category.assoc] using congrArg
        (fun k ↦ (pullbackSymmetry (toBase W) (chartToBase W false)).hom ≫
          chartBaseChangeInclusion W (toBase W) false ≫ k) hbase
    · change chartBaseChangeInclusion W (chartToBase W false) false ≫
        ((pullbackSymmetry (toBase W) (chartToBase W false)).hom ≫
          (chartBaseChangeInclusion W (toBase W) false ≫ f)) =
        chartBaseChangeInclusion W (chartToBase W false) false ≫
          ((pullbackSymmetry (toBase W) (chartToBase W false)).hom ≫
            (chartBaseChangeInclusion W (toBase W) false ≫ g))
      rw [chartBaseChangeInclusion_symmetry_assoc, chartBaseChangeInclusion_symmetry_assoc,
        ← chartPairInclusion_factor_right_assoc, ← chartPairInclusion_factor_right_assoc, h]
  apply (chartRightBaseChangeCover W (toBase W)).hom_ext
  intro c
  change chartRightBaseChangeInclusion W (toBase W) c ≫ f =
    chartRightBaseChangeInclusion W (toBase W) c ≫ g
  apply baseChanged_affineChart_hom_ext W (Ring W c) s
  · simpa only [Category.assoc] using congrArg
      (fun k ↦ chartRightBaseChangeInclusion W (toBase W) c ≫ k) hbase
  · change chartBaseChangeInclusion W (chartToBase W c) false ≫
      (chartRightBaseChangeInclusion W (toBase W) c ≫ f) =
      chartBaseChangeInclusion W (chartToBase W c) false ≫
        (chartRightBaseChangeInclusion W (toBase W) c ≫ g)
    simp only [← Category.assoc, ← chartPairInclusion_factor]
    simp only [chartPairInclusion_factor_right, Category.assoc, ha]

end WeierstrassCurve.CubicCharts
