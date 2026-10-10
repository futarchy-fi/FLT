/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossSectionMaps
public import FLT.Mazur.SchemeAffineCoverTestRecovery

/-!
# Covering recovery through the original reconstruction map

Factor normalized covering recovery through a sealed original chart map.
The scheme-square equality is kept explicit during specialization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison SheafPullbackMapNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued chartTestRecoveryIso coverRecoveryIso

/-- Affine covering recovery factors through the sealed original reconstruction map. -/
lemma coverRecoveryIso_test_originalMap (i : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (b : (C i).coverRing ⟶ A)
    (ha : Spec.map b ≫ Spec.map (C i).ringMap = Spec.map f) (d : Spec A ⟶ Y) (z : Spec A ⟶ X)
    (hd : Spec.map b ≫ (C i).cover = d) (hz : d ≫ p = z)
    (hf : Spec.map f ≫ (C i).base = z) :
    normalize (Spec.map b) (C i).cover (C i).cover d d hd hd
        (coverRecoveryIso C D i).hom =
      (comparison d p z hz).hom.app (openGlued C D) ≫
        (C i).sectionOriginalMap D f (Spec.map b) ha d hd
          (chartTestRecoveryIso C D i z (Spec.map f) hf).hom := by
  unfold Chart.sectionOriginalMap
  exact coverRecoveryIso_test C D i (Spec.map b) d (Spec.map f) z hd
    ha hz hf

end FLT.Mazur.SchemeAffineDescent
