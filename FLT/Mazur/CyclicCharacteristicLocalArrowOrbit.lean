/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicLocalOrbit
public import FLT.Mazur.CyclicCharacteristicProductOperationSchemes

/-!
# Local exact endpoints of the full same-chart comparison scheme

Every invertible-level test retains a common affine neighborhood on which
its full arrow endpoints differ by one finite relabeling.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- Every test of the full comparison scheme has locally relabeled endpoint morphisms. -/
theorem productScheme_local_sameChart_orbit {T : Scheme}
    (p : T ⟶ productSubgroupScheme n b b) (hn : IsUnit (n : Γ(T, ⊤))) (x : T) :
    ∃ (e : RelabelGroup n) (U : T.Opens), IsAffineOpen U ∧ x ∈ U ∧
      U.ι ≫ (p ≫ productArrowSource n b b) ≫ (normalizedRelabelAction n b e).hom =
        U.ι ≫ (p ≫ productArrowTarget n b b) := by
  apply productArrow_local_sameChart_orbit n b _ _ hn x
  refine ⟨p, ?_⟩
  apply prod.hom_ext <;>
    simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
      productArrowSource, productArrowTarget]

end FLT.Mazur.CyclicCharacteristicAtlas
