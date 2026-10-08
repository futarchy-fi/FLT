/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartTestRecovery
public import FLT.Mazur.SchemeAffineCommonBaseTestComparison

/-!
# Glued chart recovery retains the original descent transport

On the constructed common affine cover, the two actual glued chart
reconstructions differ by the original geometric descent transport. Both
the effective comparison and its reconstruction equation are derived.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private lemma reconstruct_comparison {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {x y z : A} {u v : B}
    (a : x ⟶ y) (b : x ⟶ z) (e : y ⟶ z)
    (r : F.obj y ⟶ u) (s : F.obj z ⟶ v) (t : u ⟶ v)
    (h : a ≫ e = b) (hr : F.map e ≫ s = r ≫ t) :
    F.map a ≫ r ≫ t = F.map b ≫ s := by
  rw [← hr, ← F.map_comp_assoc, h]

variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued chartTestRecoveryIso
  Chart.refinementReconstruction Chart.CrossRefinement.effectiveComparison

/-- The constructed common-cover reconstructions differ by the original descent transport. -/
lemma chartTestRecoveryIso_commonBase_reconstruction (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base) :
    let ρ := (C i).commonBaseCrossRefinement (C j) f g w
    (pullback (Spec.map ρ.ringMap)).map
        (chartTestRecoveryIso C D i (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom ≫
        ((C i).refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom ≫
        (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over).hom =
      (pullback (Spec.map ρ.ringMap)).map
          (chartTestRecoveryIso C D j (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom ≫
        ((C j).refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom := by
  let ρ := (C i).commonBaseCrossRefinement (C j) f g w
  let a := (chartTestRecoveryIso C D i
    (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom
  let b := (chartTestRecoveryIso C D j
    (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom
  have h : a ≫ (ρ.effectiveComparison D).hom = b :=
    (congrArg (a ≫ ·) ((C i).schemeTestComparison_commonBase (C j) f g w D)).symm.trans
      (chartTestRecoveryIso_comparison C D i j
        (Spec.map f ≫ (C i).base) (Spec.map f) (Spec.map g) rfl w.symm)
  exact reconstruct_comparison (pullback (Spec.map ρ.ringMap)) a b
    (ρ.effectiveComparison D).hom
    ((C i).refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom
    ((C j).refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom
    (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over).hom h
    (ρ.effectiveComparison_reconstruction D)

end FLT.Mazur.SchemeAffineDescent
