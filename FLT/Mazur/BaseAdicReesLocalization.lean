/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesOverlap
public import FLT.Mazur.ReesRelativeLocalization

/-!
# Localization of the actual relative chart rings

The original restriction to a principal source subopen exhibits the target
tensor ring as localization at that same source equation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) (V : X.affineOpens)

/-- Principal tensor-chart restriction localizes at the original source equation. -/
theorem relativeRingRestriction_isLocalization (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    let _ := Rees.relativeMapAlgebra J (chartRingRestriction f (U := U) (V := V) (X.basicOpen_le r))
    IsLocalization.Away (algebraMap Γ(X, V.1)
      (Γ(X, V.1) ⊗[R] reesAlgebra J) r) (Γ(X, U.1) ⊗[R] reesAlgebra J) := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  exact Rees.relativeAlgebraMap_isLocalization J
    (chartRingRestriction f (U := U) (V := V) (X.basicOpen_le r)) r (V.2.isLocalization_basicOpen r)

/-- Principal tensor-chart restriction has exactly the expected basic open as image. -/
lemma relativeRingRestriction_range_basicOpen (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    Set.range (Spec.map (CommRingCat.ofHom
      (relativeRingRestriction f J (U := U) (V := V) (X.basicOpen_le r)).toRingHom)) =
      (PrimeSpectrum.basicOpen (algebraMap Γ(X, V.1)
        (Γ(X, V.1) ⊗[R] reesAlgebra J) r)).1 := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  exact (relativeRingRestriction_range f J (U := U) (V := V) (X.basicOpen_le r)).trans
    (congrArg SetLike.coe (chartSpaceMap_preimage_basicOpen f J r))

end FLT.Mazur.BaseAdicRees
