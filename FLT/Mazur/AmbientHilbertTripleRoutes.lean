/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertTripleIntersection

/-!
# Full-domain triple routes for Hilbert gluing

The actual categorical pullback is identified with common-triple support.
Its canonical comparison with the next original ambient chart constructs a
route to the opposite overlap. Both factorization equations follow from
restriction compatibility and the proved common-open Hilbert cocycle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ)

/-- The full triple pullback maps into the opposite pairwise Hilbert overlap. -/
def tripleRoute (i j k : A.Index) :
    pullback (A.overlap d i j).ι (A.overlap d i k).ι ⟶ (A.overlap d j k).toScheme :=
  (A.triplePullbackIso d i j k).inv ≫
    (A.comparison d i j (A.triple i j k)
      (A.triple_le_first i j k) (A.triple_le_second i j k)).hom ≫
        A.inclusion d j (A.triple_le_opposite i j k)

/-- The triple route factors the first pair transition on the entire pullback. -/
@[reassoc]
theorem tripleRoute_first (i j k : A.Index) :
    A.tripleRoute d i j k ≫ (A.overlap d j k).ι =
      pullback.fst _ _ ≫ (A.transition d i j).hom ≫ (A.overlap d j i).ι := by
  apply (cancel_epi (A.triplePullbackIso d i j k).hom).mp
  simp only [tripleRoute, Category.assoc, Iso.hom_inv_id_assoc,
    triplePullbackIso_fst_assoc]
  rw [A.transition_restrict d i j (A.triple i j k) inf_le_left]
  change _ ≫ A.inclusion d j _ ≫ (A.support d j (A.common j k)).ι = _
  rw [A.inclusion_ι d j (A.triple_le_opposite i j k)]

/-- The opposite pair transition agrees with the second projection on the entire pullback. -/
@[reassoc]
theorem tripleRoute_second (i j k : A.Index) :
    A.tripleRoute d i j k ≫ (A.transition d j k).hom ≫ (A.overlap d k j).ι =
      pullback.snd _ _ ≫ (A.transition d i k).hom ≫ (A.overlap d k i).ι := by
  apply (cancel_epi (A.triplePullbackIso d i j k).hom).mp
  simp only [tripleRoute, Category.assoc, Iso.hom_inv_id_assoc,
    triplePullbackIso_snd_assoc]
  rw [A.transition_restrict d j k (A.triple i j k) (A.triple_le_opposite i j k),
    A.transition_restrict d i k (A.triple i j k) inf_le_right]
  rw [← Category.assoc, ← Iso.trans_hom,
    A.comparison_trans d i j k (A.triple i j k)
      (A.triple_le_first i j k) (A.triple_le_second i j k) (A.triple_le_third i j k)]

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
