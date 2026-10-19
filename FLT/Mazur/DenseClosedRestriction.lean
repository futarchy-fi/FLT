/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Restricting morphisms to closed subschemes using a dense test source

A factorization on a schematically dense source forces the defining ideal to
vanish globally. This constructs the restriction, retaining the original map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.DenseClosedRestriction

universe u
variable {T Y Z X : Scheme.{u}} (d : T ⟶ Y) (i : Z ⟶ X)
  [IsSchemeTheoreticallyDominant d] [IsClosedImmersion i]
  (f : Y ⟶ X) (g : T ⟶ Z) (h : d ≫ f = g ≫ i)

include h in
omit [IsClosedImmersion i] in
/-- Dense factorization forces all equations of the closed target to vanish. -/
theorem ideal_le : i.ker ≤ f.ker := by
  have hd : (d ≫ f).ker = f.ker := by
    rw [Scheme.Hom.ker_comp, d.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  rw [← hd, h]
  exact Scheme.Hom.le_ker_comp _ _

/-- The actual restriction obtained from the equations detected by the dense source. -/
def lift : Y ⟶ Z := IsClosedImmersion.lift i f (ideal_le d i f g h)

/-- The constructed restriction recovers the prescribed ambient morphism. -/
@[reassoc (attr := simp)] theorem lift_inclusion : lift d i f g h ≫ i = f :=
  IsClosedImmersion.lift_fac _ _ _

/-- The restriction agrees with the original map on the full dense source. -/
@[reassoc] theorem dense_lift : d ≫ lift d i f g h = g := by
  apply (cancel_mono i).mp
  rw [Category.assoc, lift_inclusion, h]

/-- The original ambient map determines the restriction uniquely. -/
theorem lift_unique (k : Y ⟶ Z) (hk : k ≫ i = f) : k = lift d i f g h := by
  apply (cancel_mono i).mp
  rw [hk, lift_inclusion]

end FLT.Mazur.DenseClosedRestriction
