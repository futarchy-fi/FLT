/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupOrbitMarking

/-!
# A compatible generator comparison determines every orbit label

The proof takes place on abstract subgroup carriers. Applications to actual
parameter families therefore need not unfold their geometric group laws.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n} (a : CompatibleIso H J)
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ F.group))
  (hH : H.ideal = E.cyclicMarkingIdeal φ) (hJ : J.ideal = F.cyclicMarkingIdeal ψ)

/-- Preserving the prescribed generator preserves all actual subgroup labels. -/
theorem CompatibleIso.orbitMarking_of_generator
    (hP : H.orbitGenerator φ hH ≫ a.subgroup.hom = J.orbitGenerator ψ hJ)
    (i : Multiplicative (ZMod n)) :
    H.orbitMarking φ hH i ≫ a.subgroup.hom = J.orbitMarking ψ hJ i := by
  have hp := congrArg (fun s ↦ s ^ i.toAdd.val) hP
  rw [← MonObj.pow_comp, orbitGenerator_pow, orbitGenerator_pow,
    ZMod.natCast_zmod_val] at hp
  exact hp

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
