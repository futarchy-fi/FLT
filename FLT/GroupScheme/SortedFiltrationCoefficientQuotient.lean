/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.SortedFiltrationFunctoriality
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The coefficient-linear quotient of a sorted integral filtration

For a supplied sorted extension killed by three, its multiplicative point
subgroup is a submodule for every coefficient action commuting with Galois.
The canonical linear quotient is surjective and Galois invariant. Its kernel
is exactly the given multiplicative point subgroup, and it is nonzero when
the integral constant-filtered quotient is nonzero.

These statements do not assert existence of a sorted extension or prove the
determinant argument needed to rule out a zero constant-filtered quotient.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

variable {H : FiniteFlatObject ZInvTwo} (S : SortedFiniteFlatExtension H)
    (hkill : KilledByQ 3 H) (k : Type*) [Ring k] [Module k H.points]
    [SMulCommClass Γ k H.points]

/-- The multiplicative point subgroup as a coefficient submodule. -/
def SortedFiniteFlatExtension.pointSubmodule : Submodule k H.points where
  carrier := S.pointSubgroup
  zero_mem' := S.pointSubgroup.zero_mem
  add_mem' := S.pointSubgroup.add_mem
  smul_mem' c _ hx := S.smul_mem_pointSubgroup hkill c hx

/-- The canonical coefficient-linear projection killing precisely the
multiplicative part of the supplied integral extension. -/
def SortedFiniteFlatExtension.coefficientProjection :
    H.points →ₗ[k] H.points ⧸ S.pointSubmodule hkill k :=
  (S.pointSubmodule hkill k).mkQ

/-- Every point of the coefficient quotient has a representative in the middle group. -/
theorem SortedFiniteFlatExtension.coefficientProjection_surjective :
    Function.Surjective (S.coefficientProjection hkill k) :=
  Submodule.mkQ_surjective _

/-- The kernel of the coefficient projection is the original multiplicative
point subgroup, with its proved coefficient-submodule structure. -/
theorem SortedFiniteFlatExtension.coefficientProjection_ker :
    LinearMap.ker (S.coefficientProjection hkill k) = S.pointSubmodule hkill k :=
  Submodule.ker_mkQ _

omit hkill [SMulCommClass Γ k H.points] [Module k H.points] [Ring k] in
/-- The difference between a point and any Galois translate lies in the
multiplicative part because the integral quotient has trivial point action. -/
theorem SortedFiniteFlatExtension.galoisDifference_mem (σ : Γ) (x : H.points) :
    σ • x - x ∈ S.pointSubgroup := by
  apply (S.extension.pointsExact _).mp
  rw [map_sub, map_smul]
  have hfix := pure_one_of_constantThree_filtration S.right S.rightFiltration σ
    (FiniteFlatObject.pointMap S.extension.quotient x)
  simpa using sub_eq_zero.mpr (by simpa using hfix)

/-- The canonical coefficient-linear quotient is invariant under every Galois element. -/
theorem SortedFiniteFlatExtension.coefficientProjection_invariant (σ : Γ) (x : H.points) :
    S.coefficientProjection hkill k (σ • x) = S.coefficientProjection hkill k x := by
  apply (Submodule.Quotient.eq _).mpr
  exact S.galoisDifference_mem σ x

/-- A nonzero integral constant-filtered quotient makes the coefficient
submodule proper; no identification of the coefficient field with `𝔽₃` is used. -/
theorem SortedFiniteFlatExtension.pointSubmodule_ne_top [Nontrivial S.right.points] :
    S.pointSubmodule hkill k ≠ ⊤ := by
  intro htop
  obtain ⟨q, hq⟩ := exists_ne (0 : S.right.points)
  obtain ⟨x, hx⟩ := S.extension.pointsSurjective q
  have hmem : x ∈ S.pointSubmodule hkill k := by rw [htop]; trivial
  have hz : FiniteFlatObject.pointMap S.extension.quotient x = 0 :=
    (S.extension.pointsExact x).mpr hmem
  exact hq (hx.symm.trans hz)

/-- The coefficient quotient is nontrivial whenever the integral quotient is nontrivial. -/
theorem SortedFiniteFlatExtension.coefficientQuotient_nontrivial
    [Nontrivial S.right.points] : Nontrivial (H.points ⧸ S.pointSubmodule hkill k) :=
  Submodule.Quotient.nontrivial_iff.mpr (S.pointSubmodule_ne_top hkill k)

end ThreeAdicPlan
