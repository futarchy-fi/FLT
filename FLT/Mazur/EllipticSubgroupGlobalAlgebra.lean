/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureFinite
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The finite global coordinate algebra of the subgroup closure

Finiteness makes the glued closure affine. Its global sections have the actual
structural valuation-ring algebra, finite and flat over a DVR, hence free.
Their rank is the dimension of their scalar extension to the fraction field.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The coordinate algebra of the entire affine Y/Z closure. -/
abbrev GlobalClosure := Γ(gluedClosure A W H 1 2, ⊤)

/-- The actual structural ring map from the valuation ring to global sections. -/
def globalClosureBaseMap : A →+* GlobalClosure A W H :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ (closureToBase A W H 1 2).appTop).hom

instance globalClosureAlgebra : Algebra A (GlobalClosure A W H) :=
  (globalClosureBaseMap A W H).toAlgebra

/-- The affine comparison preserves the given structural map. -/
@[reassoc] theorem globalClosure_toBase :
    (gluedClosure A W H 1 2).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (GlobalClosure A W H))) =
        closureToBase A W H 1 2 := by
  change (gluedClosure A W H 1 2).toSpecΓ ≫
    Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ (closureToBase A W H 1 2).appTop) = _
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Global coordinates form a finite module over the valuation ring. -/
instance globalClosure_finite : Module.Finite A (GlobalClosure A W H) := by
  apply RingHom.finite_algebraMap.mp
  change (globalClosureBaseMap A W H).Finite
  exact (closureToBase A W H 1 2).finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2)

/-- The global coordinate module inherits the actual structural flatness over a DVR. -/
instance globalClosure_flat [IsDedekindDomain A] : Module.Flat A (GlobalClosure A W H) := by
  apply RingHom.flat_algebraMap_iff.mp
  change (globalClosureBaseMap A W H).Flat
  exact (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv)).comp
      (closureToBase A W H 1 2).flat_appTop

/-- A finite flat module over the local valuation ring is free. -/
instance globalClosure_free [IsDedekindDomain A] : Module.Free A (GlobalClosure A W H) :=
  Module.free_of_flat_of_isLocalRing

/-- The integral rank is determined by the actual generic global coordinate algebra. -/
theorem globalClosure_finrank_generic [IsDedekindDomain A] :
    Module.finrank A (GlobalClosure A W H) =
      Module.finrank K (K ⊗[A] GlobalClosure A W H) :=
  (Module.finrank_baseChange (R := K) (S := A) (M' := GlobalClosure A W H)).symm

end FLT.Mazur.EllipticSubgroupChart
