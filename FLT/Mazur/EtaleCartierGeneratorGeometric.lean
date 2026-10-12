/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorCyclicMap
public import FLT.Mazur.FiniteUnramifiedFieldLength

/-!
# Geometric distinctness of etale Cartier generators

The orbit covers the subgroup. Its geometric point count is exactly its
scheme-theoretic degree, so the n powers are distinct over a separably closed
field. No faithfulness hypothesis is added to the original cyclic level.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [IsSepClosed K]
  {E : GeneralizedEllipticCurve (Spec (.of K))} {n : ℕ}
  (H : E.FiniteSubgroup n) [Etale H.carrier.hom]
  {P : 𝟙_ (Over (Spec (.of K))) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

/-- The actual geometric subgroup has n underlying points. -/
theorem etale_geometric_card : Nat.card H.carrier.left = n :=
  (FCurve.finiteUnramifiedField_rank_eq_card H.carrier.hom
    (IsLocalRing.closedPoint K)).symm.trans (H.finrank _)

include hP

/-- The n actual orbit values biject with the geometric subgroup points. -/
theorem IsCartierGenerator.geometric_orbit_bijective :
    Function.Bijective (fun i : Fin n ↦ (P ^ i.val).left (IsLocalRing.closedPoint K)) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro x
    obtain ⟨i, hi⟩ := hP.exists_orbit_point H x
    exact ⟨i, (congrArg (P ^ i.val).left
      (Subsingleton.elim (IsLocalRing.closedPoint K) (H.carrier.hom x))).trans hi⟩
  · rw [Nat.card_fin, H.etale_geometric_card]

/-- Equal geometric generator powers with exponents below n have equal exponents. -/
theorem IsCartierGenerator.geometric_powers_injective :
    Function.Injective (fun i : Fin n ↦ P ^ i.val) := by
  intro i j hij
  apply (hP.geometric_orbit_bijective H).injective
  exact congrArg (fun s : 𝟙_ (Over (Spec (.of K))) ⟶ H.carrier ↦
    s.left (IsLocalRing.closedPoint K)) hij

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
