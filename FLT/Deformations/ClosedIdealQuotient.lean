/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ProartinianQuotients
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Closed quotients of local proartinian parameter rings

Finite residue coefficients make the parameter ring compact. Quotient topology
then gives completeness for every closed ideal, while images of open ideals
supply the linear topology. No arithmetic defining ideal is assumed to exist.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace Deformation.ProartinianCat

universe u
variable {O : Type u} [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  (U : ProartinianCat O) (I : Ideal U)

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- Images of open ideals give the quotient ring its linear topology. -/
theorem quotient_isLinearTopology : IsLinearTopology (U ⧸ I) (U ⧸ I) := by
  have h := (IsLinearTopology.hasBasis_open_ideal (R := U)).map (Ideal.Quotient.mk I)
  rw [(QuotientRing.isOpenQuotientMap_mk I).map_nhds_eq, map_zero] at h
  apply IsLinearTopology.mk_of_hasBasis (U ⧸ I)
    (s := fun J : Ideal U ↦ J.map (Ideal.Quotient.mk I))
  convert h using 1
  ext J x
  exact Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- The quotient by any closed ideal remains proartinian. -/
theorem quotient_isProartinian (hI : IsClosed (I : Set U)) : IsProartinian (U ⧸ I) := by
  let : IsClosed (I.toAddSubgroup : Set U) := hI
  let : IsLinearTopology (U ⧸ I) (U ⧸ I) := quotient_isLinearTopology U I
  exact
    { isArtinianRing_quotient := fun J hJ ↦ by
        let : Finite ((U ⧸ I) ⧸ J) := AddSubgroup.quotient_finite_of_isOpen _ hJ
        infer_instance }

/-- The actual quotient by a proper closed ideal in the parameter category. -/
def closedIdealQuotient (hI : IsClosed (I : Set U)) (hne : I ≠ ⊤) : ProartinianCat O := by
  let : Nontrivial (U ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  let : IsLocalRing (U ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap O (U ⧸ I)) := by
    change IsLocalHom ((Ideal.Quotient.mk I).comp (algebraMap O U))
    infer_instance
  let : IsProartinian (U ⧸ I) := quotient_isProartinian U I hI
  exact
    { carrier := U ⧸ I
      isLocalProartinianAlgebra :=
        { toIsTopologicalRing := inferInstance
          toIsLocalRing := inferInstance
          toIsProartinian := inferInstance
          toIsLocalHom := inferInstance
          toIsResidueAlgebra := inferInstance } }

/-- The continuous projection to the constructed closed quotient. -/
def closedIdealQuotientHom (hI : IsClosed (I : Set U)) (hne : I ≠ ⊤) :
    U ⟶ closedIdealQuotient U I hI hne where
  hom :=
    { toAlgHom := Ideal.Quotient.mkₐ O I
      cont := continuous_quot_mk }

end Deformation.ProartinianCat
