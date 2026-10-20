/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ToricFiniteSubgroupRootsCompatibility

/-!
# Comparing prescribed finite subgroups on toric curves

Two finite subgroups of the same rank in a toric smooth group agree as full
closed divisors. A specified isomorphism of generalized curves transports this
comparison, retaining the actual ambient map rather than only its support.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ}

/-- Transport along a full curve isomorphism retains the subgroup and its actual inclusion. -/
def transportCompatibleIso (H : E.FiniteSubgroup n) (c : E ≅ F) :
    CompatibleIso H (H.transport c) where
  curve := c
  subgroup := Iso.refl H.carrier
  isMonHom := inferInstanceAs (IsMonHom (𝟙 H.carrier))
  compatible := by
    rw [transport_curveMap]
    exact (Category.id_comp _).symm

variable {K : Type} [Field K] {E F : GeneralizedEllipticCurve (Spec (.of K))}
  [NeZero n]

/-- Two original subgroups of the same toric group have the same complete defining ideal. -/
theorem ideal_eq_of_toric (H J : E.FiniteSubgroup n)
    (e : MultiplicativeGroupScheme.gm K ≅ E.group) [IsMonHom e.hom] : H.ideal = J.ideal :=
  (ToricFiniteSubgroupRootsClassification.ideal_eq_roots H e).trans
    (ToricFiniteSubgroupRootsClassification.ideal_eq_roots J e).symm

/-- The classification gives a compatible isomorphism between arbitrary same-rank subgroups. -/
def toricCompatibleIso (H J : E.FiniteSubgroup n)
    (e : MultiplicativeGroupScheme.gm K ≅ E.group) [IsMonHom e.hom] : CompatibleIso H J :=
  (ToricFiniteSubgroupRootsClassification.compatibleIso H e).trans
    (ToricFiniteSubgroupRootsClassification.compatibleIso J e).symm

/-- Comparison of arbitrary toric subgroups retains any specified full-curve isomorphism. -/
def toricCompatibleIsoOver (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n)
    (c : E ≅ F) (e : MultiplicativeGroupScheme.gm K ≅ F.group) [IsMonHom e.hom] :
    CompatibleIso H J :=
  (H.transportCompatibleIso c).trans ((H.transport c).toricCompatibleIso J e)

/-- The comparison's ambient map is exactly the supplied generalized-curve isomorphism. -/
theorem toricCompatibleIsoOver_curve (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n)
    (c : E ≅ F) (e : MultiplicativeGroupScheme.gm K ≅ F.group) [IsMonHom e.hom] :
    (H.toricCompatibleIsoOver J c e).curve = c := by
  simp only [toricCompatibleIsoOver, transportCompatibleIso, toricCompatibleIso,
    CompatibleIso.trans, CompatibleIso.symm,
    ToricFiniteSubgroupRootsClassification.compatibleIso_curve, Iso.refl_symm, Iso.trans_refl]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
