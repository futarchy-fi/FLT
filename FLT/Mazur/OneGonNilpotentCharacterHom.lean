/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNilpotentDiagonalizableLift
public import FLT.Mazur.WeierstrassDiagonalizableMonHom

/-!
# Actual character-group homomorphisms on nilpotent smoothings

The global corrected lift is a homomorphism of the original group schemes.
It is uniquely characterized by its prescribed reduction. This construction
applies in particular to the nonetale roots-of-unity character group.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.OneGonSmoothing

open WeierstrassIntegralChart WeierstrassDiagonalizableDefect DiagonalizableCobar
open CharacterSchemeBaseChange

local notation "SmoothPoints" => WeierstrassDiagonalizableDefect.Points

variable {R G : Type} [CommRing R] [AddCommGroup G]

instance characterModelCommGrp : CommGrpObj (model R G) :=
  inferInstanceAs (CommGrpObj ((Spec (.of (AddMonoidAlgebra R G))).asOver (Spec (.of R))))

variable (t : R) (ht : IsNilpotent t) (I : Ideal R) (hI : I ^ 2 = ⊥)
  (p : SmoothPoints (equation t) (AddMonoidAlgebra (R ⧸ I) G))
  (hp : defect (equation t) p = 1)

include ht hI hp in
/-- A unique actual group-scheme homomorphism lifts the original multiplicative map. -/
theorem nilpotent_existsUnique_isMonHom :
    ∃! q : SmoothPoints (equation t) (AddMonoidAlgebra R G),
      smoothAlgebraReduction (equation t) (coefficientReduction R G I) q = p ∧ IsMonHom q := by
  simpa only [← defect_eq_one_iff_isMonHom] using
    nilpotent_diagonalizable_existsUnique_lift t ht I hI p hp

/-- The uniquely determined actual map, before bundling its group-homomorphism proof. -/
def nilpotentCharacterLift : SmoothPoints (equation t) (AddMonoidAlgebra R G) :=
  (nilpotent_existsUnique_isMonHom t ht I hI p hp).exists.choose

/-- The lift retains the complete specified coefficient reduction. -/
theorem nilpotentCharacterLift_reduction :
    smoothAlgebraReduction (equation t) (coefficientReduction R G I)
      (nilpotentCharacterLift t ht I hI p hp) = p :=
  (nilpotent_existsUnique_isMonHom t ht I hI p hp).exists.choose_spec.1

instance nilpotentCharacterLift_isMonHom : IsMonHom (nilpotentCharacterLift t ht I hI p hp) :=
  (nilpotent_existsUnique_isMonHom t ht I hI p hp).exists.choose_spec.2

/-- The constructed lift as a morphism of the original commutative group schemes. -/
def nilpotentCharacterHom : CommGrp.mk (model R G) ⟶ integralSmoothGroup (equation t) :=
  InducedCategory.homMk (Grp.homMk (nilpotentCharacterLift t ht I hI p hp))

/-- Every original group-scheme lift with this reduction equals the constructed lift. -/
theorem nilpotentCharacterLift_unique
    (q : SmoothPoints (equation t) (AddMonoidAlgebra R G)) [IsMonHom q]
    (hq : smoothAlgebraReduction (equation t) (coefficientReduction R G I) q = p) :
    q = nilpotentCharacterLift t ht I hI p hp :=
  (nilpotent_existsUnique_isMonHom t ht I hI p hp).unique ⟨hq, inferInstance⟩
    ⟨nilpotentCharacterLift_reduction t ht I hI p hp, inferInstance⟩

end FLT.Mazur.OneGonSmoothing
