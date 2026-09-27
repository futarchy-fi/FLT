/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Naturality of Weierstrass model transport

A change of coordinates defined over the base gives compatible point-group
isomorphisms over every field extension, with no topological hypotheses.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.Point
variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [DecidableEq L] [DecidableEq M]
/-- Change of Weierstrass coordinates after extension of the base field. -/
noncomputable def equivVariableChangeOver (W : WeierstrassCurve K) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange K) : ((C • W)⁄L).Point ≃+ (W⁄L).Point := by
  let : (W.baseChange L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic
  exact (equivOfEq (WeierstrassCurve.map_variableChange W C (algebraMap K L)).symm).trans
    (equivVariableChange (W.baseChange L) (C.map (algebraMap K L)))
/-- Coordinate changes defined over the base commute with field maps. -/
theorem map_equivVariableChangeOver (W : WeierstrassCurve K) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange K) (f : L →ₐ[K] M) (P : ((C • W)⁄L).Point) :
    map f (equivVariableChangeOver W C P) = equivVariableChangeOver W C (map f P) := by
  let : (W.baseChange L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic
  let : (W.baseChange M).IsElliptic := inferInstanceAs (W.map (algebraMap K M)).IsElliptic
  cases P with
  | zero => simp only [← zero_def, map_zero, AddEquiv.map_zero]
  | some x y h =>
    unfold equivVariableChangeOver
    erw [AddEquiv.trans_apply, AddEquiv.trans_apply, equivOfEq_some, map_some,
      equivOfEq_some, equivVariableChange_some, some.injEq]
    constructor <;>
      simp [WeierstrassCurve.VariableChange.map, map_add, map_mul, map_pow, f.commutes]
/-- Transport points from a fixed Weierstrass model to an isomorphic model over any extension. -/
noncomputable def modelEquivOver (V E : WeierstrassCurve K) [V.IsElliptic]
    (C : WeierstrassCurve.VariableChange K) (h : C • V = E) : (V⁄L).Point ≃+ (E⁄L).Point :=
  (equivVariableChangeOver V C).symm.trans
    (equivOfEq (congrArg (fun W : WeierstrassCurve K ↦ W.baseChange L) h))

/-- Transport through a fixed model isomorphism commutes with every base-linear field map. -/
theorem map_modelEquivOver (V E : WeierstrassCurve K) [V.IsElliptic]
    (C : WeierstrassCurve.VariableChange K) (h : C • V = E)
    (f : L →ₐ[K] M) (P : (V⁄L).Point) :
    map f (modelEquivOver V E C h P) = modelEquivOver V E C h (map f P) := by
  subst E
  change map f ((equivVariableChangeOver V C).symm P) =
    (equivVariableChangeOver V C).symm (map f P)
  apply (equivVariableChangeOver V C).injective
  rw [← map_equivVariableChangeOver, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end WeierstrassCurve.Affine.Point
