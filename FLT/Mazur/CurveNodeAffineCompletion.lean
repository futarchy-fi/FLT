/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveNode
public import FLT.Mazur.LocalizedAdicCompletion
public import Mathlib.RingTheory.Localization.AtPrime.Basic
/-!
# The completed stalk of an affine scheme at a closed point

The canonical stalk algebra and the scalars induced by Spec of the structure
map agree. Localization therefore identifies the actual completed stalk
with the affine algebra completed at its maximal ideal.
-/

open CategoryTheory AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.CurveNodeAffineCompletion
open FCurve.CurveNode
variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]
variable (x : Spec (.of A))
/-- The canonical algebra of the affine ring on its actual stalk. -/
local instance stalkAlgebra : Algebra A (LocalRing x) :=
  StructureSheaf.stalkAlgebra A x
theorem scalar_spec : scalarMap (Spec.map (CommRingCat.ofHom (algebraMap K A))) x =
    (algebraMap A (LocalRing x)).comp (algebraMap K A) := by
  unfold scalarMap
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl
/-- The actual affine stalk completion, with the specified base-field scalars. -/
def equivalence [x.asIdeal.IsMaximal] :
    letI := localAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K A))) x
    AdicCompletion x.asIdeal A ≃ₐ[K] CompletedLocalRing x := by
  letI := localAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K A))) x
  letI : IsScalarTower K A (LocalRing x) := IsScalarTower.of_algebraMap_eq' (scalar_spec K A x)
  letI : IsLocalization.AtPrime (LocalRing x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A x
  exact LocalizedAdicCompletion.equivalence (K := K) x.asIdeal (LocalRing x)
theorem isNode_iff [x.asIdeal.IsMaximal] :
    IsNode (Spec.map (CommRingCat.ofHom (algebraMap K A))) x ↔
      Nonempty (AdicCompletion x.asIdeal A ≃ₐ[K] Model K) := by
  let := localAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K A))) x
  constructor
  · rintro ⟨e⟩
    exact ⟨(equivalence K A x).trans e⟩
  · rintro ⟨e⟩
    exact ⟨(equivalence K A x).symm.trans e⟩
end FLT.Mazur.CurveNodeAffineCompletion
