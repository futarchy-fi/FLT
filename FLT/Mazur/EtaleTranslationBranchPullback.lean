/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleTranslationBranchMaps
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The branch is an actual open in the changed translation

The tensor spectrum is the scheme pullback. Its principal branch therefore
embeds into the actual base-changed translation, preserving both projections.
This distinguishes a translation refinement from merely changing coefficients.
-/

@[expose] public noncomputable section
open TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace FLT.Mazur.EtaleTranslationBranch
universe u
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (e : S ⊗[R] B)
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap R B))

/-- The branch inclusion in the actual scheme pullback, not just its tensor coordinates. -/
def toBaseChange : source e ⟶ pullback b g := inclusion e ≫ (pullbackSpecIso R S B).inv

instance toBaseChange_isOpenImmersion : IsOpenImmersion (toBaseChange e) := by
  unfold toBaseChange
  infer_instance

/-- The first pullback projection is exactly the finite branch's new base map. -/
@[reassoc]
theorem toBaseChange_fst : toBaseChange e ≫ pullback.fst b g = toBase e := by
  rw [toBaseChange, Category.assoc, pullbackSpecIso_inv_fst']
  rw [inclusion, toBase, ← Spec.map_comp]
  congr 1

/-- The second projection is exactly the map to the original translation. -/
@[reassoc]
theorem toBaseChange_snd : toBaseChange e ≫ pullback.snd b g = toOriginal e := by
  rw [toBaseChange, Category.assoc, pullbackSpecIso_inv_snd]
  rw [inclusion, toOriginal, ← Spec.map_comp]
  congr 1

/-- The canonical lift from the original structural square is the constructed open inclusion. -/
theorem toBaseChange_eq_lift :
    toBaseChange e = pullback.lift (toBase e) (toOriginal e) (base_square e).symm := by
  apply pullback.hom_ext
  · rw [toBaseChange_fst, pullback.lift_fst]
  · rw [toBaseChange_snd, pullback.lift_snd]

/-- Every further open branch remains an actual open of the same changed translation. -/
instance restricted_toBaseChange_isOpenImmersion (U : (source e).Opens) :
    IsOpenImmersion (U.ι ≫ toBaseChange e) := inferInstance

/-- Restricting the branch retains both independent original coordinates. -/
theorem restricted_toBaseChange_projections (U : (source e).Opens) :
    U.ι ≫ toBaseChange e ≫ pullback.fst b g = U.ι ≫ toBase e ∧
      U.ι ≫ toBaseChange e ≫ pullback.snd b g = U.ι ≫ toOriginal e := by
  rw [toBaseChange_fst, toBaseChange_snd]
  exact ⟨rfl, rfl⟩

end FLT.Mazur.EtaleTranslationBranch
