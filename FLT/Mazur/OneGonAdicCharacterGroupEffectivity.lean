/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterIntrinsicReduction
public import FLT.Mazur.WeierstrassAdicCharacterIdentityDetection

/-!
# Effective original character-group homomorphisms over the complete base

The full multiplication defect vanishes because all its finite restrictions
vanish. This proves the original multiplication and identity equations and
bundles the constructed map as an actual group-scheme homomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MonoidalCategory

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart WeierstrassDiagonalizableDefect
open CharacterSchemeBaseChange

variable {R G : Type} [CommRing R] [AddCommGroup G] [Finite G]
  (I : Ideal R) [IsAdicComplete I R] (t : R) (ht : t ∈ I)
  (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- The full original complete-base multiplication defect is the smooth identity. -/
theorem effectiveSmoothOver_defect : defect (equation t) (effectiveSmoothOver I t ht g) = 1 :=
  eq_one_of_adic_reduction I (equation t) _ (effectiveSmoothOver_defect_reduction I t ht g)

instance effectiveSmoothOver_isMonHom : IsMonHom (effectiveSmoothOver I t ht g) :=
  (defect_eq_one_iff_isMonHom (equation t) _).mp (effectiveSmoothOver_defect I t ht g)

/-- The actual effective homomorphism of the original commutative group schemes. -/
def effectiveCharacterHom : CommGrp.mk (model R G) ⟶ integralSmoothGroup (equation t) :=
  InducedCategory.homMk (Grp.homMk (effectiveSmoothOver I t ht g))

/-- The constructed homomorphism retains the original finite-stage homomorphisms. -/
theorem effectiveCharacterHom_reduction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction (G := G) I m)) ≫
      (effectiveCharacterHom I t ht g).hom.hom.hom.left =
        (tower I t ht g m).hom.hom.hom.left ≫ smoothProjection I t m :=
  effectiveSmooth_reduction I t ht g m

/-- The identity equation uses the independently constructed original group structures. -/
theorem effectiveSmoothOver_one :
    η[model R G] ≫ effectiveSmoothOver I t ht g = η[(integralSmoothGroup (equation t)).X] :=
  IsMonHom.one_hom (effectiveSmoothOver I t ht g)

/-- The multiplication equation uses the full original categorical product and group law. -/
theorem effectiveSmoothOver_mul :
    μ[model R G] ≫ effectiveSmoothOver I t ht g =
      (effectiveSmoothOver I t ht g ⊗ₘ effectiveSmoothOver I t ht g) ≫
        μ[(integralSmoothGroup (equation t)).X] :=
  IsMonHom.mul_hom (effectiveSmoothOver I t ht g)

end FLT.Mazur.OneGonAdicCharacterTower
