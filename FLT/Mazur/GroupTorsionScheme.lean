/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelKernelLocus

/-!
# The represented torsion equation of a scheme group

The equalizer of the n-th power map and the identity section represents the
n-torsion condition on every test scheme. For a separated group it is closed.
This supplies an actual target for auxiliary markings before proving fullness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.GroupTorsionScheme

variable {S : Scheme} (E : Over S) [GrpObj E] (n : ℕ)

/-- The n-th power operation as an actual scheme map. -/
def powerMap : E ⟶ E := (𝟙 E) ^ n

/-- Its test points are the n-th powers of the original group-valued points. -/
@[reassoc] theorem comp_powerMap {U : Over S} (f : U ⟶ E) :
    f ≫ powerMap E n = f ^ n := by
  simp only [powerMap, MonObj.comp_pow, Category.comp_id]

/-- The full scheme-theoretic n-torsion equation. -/
def scheme : Over S := equalizer (powerMap E n) 1

/-- The actual inclusion of the torsion equation into the group. -/
def inclusion : scheme E n ⟶ E := equalizer.ι _ _

/-- Every point of the constructed torsion scheme is killed by n. -/
theorem inclusion_pow : inclusion E n ^ n = 1 := by
  rw [← comp_powerMap, inclusion, equalizer.condition, MonObj.comp_one]

/-- The torsion equation is closed when the original group is separated. -/
instance inclusion_closed [IsSeparated E.hom] : IsClosedImmersion (inclusion E n).left :=
  isClosedImmersion_equalizer_ι_left (powerMap E n) 1

/-- A killed section factors through the actual torsion equation. -/
def lift {U : Over S} (f : U ⟶ E) (hf : f ^ n = 1) : U ⟶ scheme E n :=
  equalizer.lift f (by rw [comp_powerMap, hf, MonObj.comp_one])

/-- The factorization retains the original section. -/
@[reassoc (attr := simp)] theorem lift_inclusion {U : Over S} (f : U ⟶ E)
    (hf : f ^ n = 1) : lift E n f hf ≫ inclusion E n = f := equalizer.lift_ι _ _

/-- The torsion scheme represents the killed-section condition, including nilpotents. -/
def representation (U : Over S) :
    (U ⟶ scheme E n) ≃ {f : U ⟶ E // f ^ n = 1} where
  toFun g := ⟨g ≫ inclusion E n, by rw [← MonObj.comp_pow, inclusion_pow, MonObj.comp_one]⟩
  invFun f := lift E n f.val f.property
  left_inv g := by
    apply equalizer.hom_ext
    exact lift_inclusion E n _ _
  right_inv f := Subtype.ext (lift_inclusion E n _ _)

/-- The torsion representation commutes with changing the test scheme. -/
theorem representation_comp {U V : Over S} (f : U ⟶ V) (g : V ⟶ scheme E n) :
    (representation E n U (f ≫ g)).val = f ≫ (representation E n V g).val :=
  Category.assoc _ _ _

end FLT.Mazur.GroupTorsionScheme
