/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNilpotentCharacterHom
public import FLT.Mazur.WeierstrassCharacterCoefficientNaturality

/-!
# Unique character lifts along specified surjective coefficient maps

The quotient-kernel algebra equivalence transports the original map into the
proved square-zero lifting theorem. Its inverse recovers the specified
coefficient map, so no compatibility or underlying lift is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.OneGonSmoothing

open WeierstrassIntegralChart WeierstrassDiagonalizableDefect DiagonalizableCobar

local notation "SmoothPoints" => WeierstrassDiagonalizableDefect.Points

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S G : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup G]
  (t : R) (ht : IsNilpotent t)

/-- The actual character coefficient map for the specified algebra structure. -/
def characterCoefficientMap : AddMonoidAlgebra R G →ₐ[R] AddMonoidAlgebra S G :=
  AddMonoidAlgebra.mapAlgHom G (IsScalarTower.toAlgHom R R S)

variable (hs : Function.Surjective (algebraMap R S))
  (hk : RingHom.ker (algebraMap R S) ^ 2 = ⊥)
  (p : SmoothPoints (equation t) (AddMonoidAlgebra S G))
  (hp : defect (equation t) p = 1)

include ht hs hk hp in
/-- A unique original multiplicative lift exists for the specified surjection. -/
theorem nilpotent_surjective_existsUnique_lift :
    ∃! q : SmoothPoints (equation t) (AddMonoidAlgebra R G),
      smoothAlgebraReduction (equation t) (characterCoefficientMap (R := R) (S := S)) q = p ∧
        IsMonHom q := by
  let I := RingHom.ker (algebraMap R S)
  let e : (R ⧸ I) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := IsScalarTower.toAlgHom R R S) hs
  let c := AddMonoidAlgebra.mapAlgHom G e.symm.toAlgHom
  have hc : c.comp (characterCoefficientMap (R := R) (S := S)) =
      coefficientReduction R G I := by
    ext a
    simp [c, characterCoefficientMap, coefficientReduction]
  have hp' : defect (equation t) (smoothAlgebraReduction (equation t) c p) = 1 := by
    rw [defect_coefficientMap, hp, map_one]
  obtain ⟨q, hq, hu⟩ := nilpotent_existsUnique_isMonHom t ht I hk
    (smoothAlgebraReduction (equation t) c p) hp'
  have hq' : smoothAlgebraReduction (equation t)
      (characterCoefficientMap (R := R) (S := S)) q = p := by
    apply coefficientEquiv_injective (equation t) e.symm
    rw [← smoothAlgebraReduction_comp, hc]
    exact hq.1
  refine ⟨q, ⟨hq', hq.2⟩, ?_⟩
  intro q' hq'
  apply hu q'
  refine ⟨?_, hq'.2⟩
  rw [← hc, smoothAlgebraReduction_comp, hq'.1]

end FLT.Mazur.OneGonSmoothing
