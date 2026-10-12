/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientPointTransport
public import FLT.Mazur.GrassmannianAmbientChartIndex

/-!
# Original ambient chart points and split chart points

Changing ambient coordinates identifies the split quotient chart with precisely
the original quotient points whose selected summand is a quotient basis.
The equivalence preserves the full relation submodule through the ambient change.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R M κ : Type*} [CommRing R] [AddCommGroup M] [Module R M] {d : ℕ}

/-- Original quotient points for which this actual selected ambient summand is a basis. -/
def AmbientChartPoint (i : AmbientChartIndex R M κ d) :=
  {N : Module.Grassmannian R M d //
    Function.Bijective (N.toSubmodule.mkQ.comp (ambientChartSelected i))}

/-- Transport an original ambient chart point into split coordinates. -/
def ambientChartPointToSplit (i : AmbientChartIndex R M κ d) (N : AmbientChartPoint i) :
    SplitChart R (κ → R) d := by
  refine ⟨ambientTransportPoint i.symm N.val, ?_⟩
  let e := ambientTransportQuotientEquiv i.symm N.val
  have he : e.toLinearMap.comp
      ((ambientTransportPoint i.symm N.val).toSubmodule.mkQ.comp (LinearMap.inl R _ _)) =
      N.val.toSubmodule.mkQ.comp (ambientChartSelected i) := by
    apply LinearMap.ext
    intro x
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _
      (ambientTransportQuotient_surjective i.symm N.val) (x, 0)
  have h : Function.Bijective (e.toLinearMap.comp
      ((ambientTransportPoint i.symm N.val).toSubmodule.mkQ.comp (LinearMap.inl R _ _))) := by
    rw [he]
    exact N.property
  exact (Function.Bijective.of_comp_iff' e.bijective _).mp h

/-- Transport a split quotient chart point to the original ambient module. -/
def ambientChartPointOfSplit (i : AmbientChartIndex R M κ d) (N : SplitChart R (κ → R) d) :
    AmbientChartPoint i := by
  refine ⟨ambientTransportPoint i N.val, ?_⟩
  let e := ambientTransportQuotientEquiv i N.val
  have he : e.toLinearMap.comp
      ((ambientTransportPoint i N.val).toSubmodule.mkQ.comp (ambientChartSelected i)) =
      N.val.toSubmodule.mkQ.comp (LinearMap.inl R _ _) := by
    apply LinearMap.ext
    intro x
    change ambientTransportQuotientEquiv i N.val
      (Submodule.Quotient.mk (i (x, 0))) = N.val.toSubmodule.mkQ (x, 0)
    rw [ambientTransportQuotientEquiv, LinearMap.quotKerEquivOfSurjective_apply_mk]
    change N.val.toSubmodule.mkQ (i.symm (i (x, 0))) = _
    rw [LinearEquiv.symm_apply_apply]
  have h : Function.Bijective (e.toLinearMap.comp
      ((ambientTransportPoint i N.val).toSubmodule.mkQ.comp (ambientChartSelected i))) := by
    rw [he]
    exact N.property
  exact (Function.Bijective.of_comp_iff' e.bijective _).mp h

/-- Passing to split coordinates and back preserves every original quotient relation. -/
theorem ambientChartPointOfSplit_toSplit (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint i) :
    ambientChartPointOfSplit i (ambientChartPointToSplit i N) = N := by
  apply Subtype.ext
  exact ambientTransportPoint_symm i.symm N.val

/-- Passing to ambient coordinates and back preserves every split quotient relation. -/
theorem ambientChartPointToSplit_ofSplit (i : AmbientChartIndex R M κ d)
    (N : SplitChart R (κ → R) d) :
    ambientChartPointToSplit i (ambientChartPointOfSplit i N) = N := by
  apply Subtype.ext
  exact ambientTransportPoint_symm i N.val

/-- The actual original ambient chart points are exactly the split quotient chart points. -/
def ambientChartPointEquiv (i : AmbientChartIndex R M κ d) :
    SplitChart R (κ → R) d ≃ AmbientChartPoint i where
  toFun := ambientChartPointOfSplit i
  invFun := ambientChartPointToSplit i
  left_inv := ambientChartPointToSplit_ofSplit i
  right_inv := ambientChartPointOfSplit_toSplit i

end FLT.Mazur.GrassmannianChart
