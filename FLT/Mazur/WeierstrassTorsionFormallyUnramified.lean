/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FormallyUnramifiedQuotientCriterion
public import FLT.Mazur.GroupTorsionScheme
public import FLT.Mazur.WeierstrassSquareZeroTorsionRigidity

/-!
# Formal unramifiedness of prime-to-characteristic torsion

The full represented torsion equation is formally unramified when its index
is invertible in the coefficient ring. The proof uses uniqueness of actual
scheme-valued group points, including over nonreduced test algebras.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The actual torsion equalizer is formally unramified for every invertible index. -/
theorem integralTorsion_formallyUnramified (n : ℕ) (hn : IsUnit (n : R)) :
    FormallyUnramified (GroupTorsionScheme.scheme (integralCurveGroup W hΔ).X n).hom := by
  let E := (integralCurveGroup W hΔ).X
  let T := GroupTorsionScheme.scheme E n
  apply FormallyUnramifiedQuotientCriterion.of_quotient_hom_ext
  intro A _ I hI g₁ g₂ hred hbase
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g₁ ≫ T.hom)
  let _ : Algebra R A := φ.hom.toAlgebra
  let p : Over.mk (Spec.map φ) ⟶ T := Over.homMk g₁ hφ.symm
  let q : Over.mk (Spec.map φ) ⟶ T := Over.homMk g₂ (hbase.symm.trans hφ.symm)
  have hnA : IsUnit (n : A) := by simpa using hn.map (algebraMap R A)
  have he : p ≫ GroupTorsionScheme.inclusion E n =
      q ≫ GroupTorsionScheme.inclusion E n := by
    apply squareZero_torsion_injective W hΔ I hI n hnA
    · exact (GroupTorsionScheme.representation E n _ p).property
    · exact (GroupTorsionScheme.representation E n _ q).property
    · apply Over.OverMorphism.ext
      exact congrArg (fun g ↦ g ≫ (GroupTorsionScheme.inclusion E n).left) hred
  have hpq : p = q := CategoryTheory.Limits.equalizer.hom_ext he
  exact congrArg Over.Hom.left hpq

end FLT.Mazur.WeierstrassIntegralChart
