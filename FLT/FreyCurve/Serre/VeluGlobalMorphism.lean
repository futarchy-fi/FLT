/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluRationalDomainCover
public import FLT.Mazur.WeierstrassIntegralSeparated
public import FLT.Mazur.WholeDomainRationalMap

/-!
# A global morphism for the original Vélu formulas

Full scheme-domain coverage glues the original regular representatives to a
unique morphism of the actual projective cubics.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.WeierstrassIntegralChart FLT.Mazur.WholeDomainRationalMap

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

local instance targetSeparated : (integralCurve (curve E G)).IsSeparated := by
  rw [Scheme.isSeparated_iff,
    ← Limits.terminal.comp_from (integralCurveStructure (curve E G))]
  infer_instance

/-- The global morphism of the original source and the exact original Vélu target. -/
def veluGlobalMorphism : integralCurve E ⟶ integralCurve (curve E G) :=
  globalHom (veluSchemeRationalMap E G hodd) (veluSchemeRationalMap_domain_eq_top E G hodd)

/-- The global morphism retains the original rational map. -/
theorem veluGlobalMorphism_toRationalMap :
    (veluGlobalMorphism E G hodd).toRationalMap = veluSchemeRationalMap E G hodd :=
  globalHom_toRationalMap _ _

/-- Its generic restriction is exactly the original generic Vélu formula. -/
@[reassoc] theorem veluGlobalMorphism_generic :
    (integralCurve E).fromSpecStalk (genericPoint (integralCurve E)) ≫
        veluGlobalMorphism E G hodd = veluSchemeGenericMorphism E G hodd := by
  have h := congrArg Scheme.RationalMap.fromFunctionField
    (veluGlobalMorphism_toRationalMap E G hodd)
  rw [veluSchemeRationalMap_fromFunctionField] at h
  change (veluGlobalMorphism E G hodd).toPartialMap.fromSpecStalkOfMem _ = _ at h
  rwa [Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap] at h

/-- Every regular representative is the restriction of the actual global morphism. -/
@[reassoc] theorem veluGlobalMorphism_representative
    (p : (integralCurve E).PartialMap (integralCurve (curve E G)))
    (hp : p.toRationalMap = veluSchemeRationalMap E G hodd) :
    p.domain.ι ≫ veluGlobalMorphism E G hodd = p.hom :=
  representative_globalHom _ _ p hp

/-- The original rational formulas determine the global scheme morphism uniquely. -/
theorem veluGlobalMorphism_unique (f : integralCurve E ⟶ integralCurve (curve E G))
    (hf : f.toRationalMap = veluSchemeRationalMap E G hodd) : f = veluGlobalMorphism E G hodd :=
  globalHom_unique _ _ f hf

end WeierstrassCurve.Velu
