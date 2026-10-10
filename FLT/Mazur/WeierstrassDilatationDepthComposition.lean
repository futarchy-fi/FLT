/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationDepthTransition

/-!
# Composition of actual changes of divided depth

The depth maps compose on the actual coordinate algebras and on their spectra.
Every change retains the contraction to the same original projective cubic.
This supplies the transition laws for finite iterations of the divided charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  (π : R) (k l m : ℕ) (hπ : π ≠ 0) (hkl : k ≤ l) (hlm : l ≤ m)
  (W : WeierstrassCurve R) (b3 b4 b6 c3 c4 c6 d3 d4 d6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
  (H3 : W.a₃ = π ^ l * c3) (H4 : W.a₄ = π ^ l * c4)
  (H6 : W.a₆ = (π ^ l) ^ 2 * c6)
  (J3 : W.a₃ = π ^ m * d3) (J4 : W.a₄ = π ^ m * d4)
  (J6 : W.a₆ = (π ^ m) ^ 2 * d6)

/-- A depth change with no change in depth is the actual identity map. -/
theorem depthTransition_self :
    depthTransition π k k hπ le_rfl W b3 b4 b6 b3 b4 b6 h3 h4 h6 h3 h4 h6 =
      AlgHom.id R (Coordinate W (π ^ k) b3 b4 b6) := by
  apply hom_ext
  · simp only [depthTransition_x, Nat.sub_self, pow_zero, map_one, one_mul,
      AlgHom.id_apply]
  · simp only [depthTransition_y, Nat.sub_self, pow_zero, map_one, one_mul,
      AlgHom.id_apply]

/-- Two successive actual depth changes equal the direct depth change. -/
theorem depthTransition_comp :
    (depthTransition π l m hπ hlm W c3 c4 c6 d3 d4 d6 H3 H4 H6 J3 J4 J6).comp
        (depthTransition π k l hπ hkl W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6) =
      depthTransition π k m hπ (hkl.trans hlm) W b3 b4 b6 d3 d4 d6
        h3 h4 h6 J3 J4 J6 := by
  have hd : l - k + (m - l) = m - k := by omega
  apply hom_ext
  · simp only [AlgHom.comp_apply, depthTransition_x, map_mul, AlgHom.commutes]
    rw [← mul_assoc, ← map_mul, ← pow_add, hd]
  · simp only [AlgHom.comp_apply, depthTransition_y, map_mul, AlgHom.commutes]
    rw [← mul_assoc, ← map_mul, ← pow_add, hd]

/-- The actual scheme morphism from a deeper divided chart to a shallower one. -/
def depthTransitionMorphism :
    Spec (.of (Coordinate W (π ^ l) c3 c4 c6)) ⟶
      Spec (.of (Coordinate W (π ^ k) b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom
    (depthTransition π k l hπ hkl W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6).toRingHom)

/-- Changing depth preserves the actual contraction to the original projective cubic. -/
@[reassoc] theorem depthTransitionMorphism_contraction :
    depthTransitionMorphism π k l hπ hkl W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6 ≫
        toCurve W (π ^ k) b3 b4 b6 h3 h4 h6 =
      toCurve W (π ^ l) c3 c4 c6 H3 H4 H6 := by
  change Spec.map _ ≫ (Spec.map _ ≫ _) = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom)
    (depthTransition_fromOriginal π k l hπ hkl W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6)

/-- The scheme transition maps obey the same finite-iteration composition law. -/
@[reassoc] theorem depthTransitionMorphism_comp :
    depthTransitionMorphism π l m hπ hlm W c3 c4 c6 d3 d4 d6 H3 H4 H6 J3 J4 J6 ≫
        depthTransitionMorphism π k l hπ hkl W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6 =
      depthTransitionMorphism π k m hπ (hkl.trans hlm) W b3 b4 b6 d3 d4 d6
        h3 h4 h6 J3 J4 J6 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom)
    (depthTransition_comp π k l m hπ hkl hlm W b3 b4 b6 c3 c4 c6 d3 d4 d6
      h3 h4 h6 H3 H4 H6 J3 J4 J6)

end FLT.Mazur.WeierstrassDilatation
