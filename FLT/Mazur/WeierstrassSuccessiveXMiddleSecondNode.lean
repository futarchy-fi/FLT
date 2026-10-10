/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTransport
public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeEquiv
public import FLT.Mazur.WeierstrassSuccessiveXMiddleTangentSwitch

/-!
# The second ordered attachment is the same actual node neighborhood

The full tangent involution identifies the open at -v (the original v-open)
with the first tangent open. The original u is retained on both node charts.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c

/-- The actual second tangent open, with the sign fixed by the tangent involution. -/
abbrev MiddleSecondOpen := Localization.Away (-coord W 0 0 0 0 c 1)

/-- The full tangent involution exchanges the two original principal opens. -/
def middleTangentOpenEquiv : MiddleFirstOpen W c ≃ₐ[R] MiddleSecondOpen W c :=
  PrincipalOpenTransport.equiv (middleTangentEquiv W c h2) _ _
    (middleTangentEquiv_first W c h2)

/-- Every original function follows the actual tangent involution on the overlap. -/
@[simp] theorem middleTangentOpenEquiv_base (q : A) :
    middleTangentOpenEquiv W c h2 (algebraMap A _ q) =
      algebraMap A (MiddleSecondOpen W c) (middleTangentEquiv W c h2 q) :=
  PrincipalOpenTransport.equiv_base _ _ _ _ _

/-- The entire second attachment neighborhood is an actual localized incidence node. -/
def middleSecondNodeEquiv : MiddleSecondOpen W c ≃ₐ[R] MiddleNodeOpen c :=
  (middleTangentOpenEquiv W c h2).symm.trans (middleFirstNodeEquiv W c h2 ha)

/-- Both ordered node charts keep the original horizontal generator. -/
theorem middleSecondNodeEquiv_u :
    middleSecondNodeEquiv W c h2 ha
      (algebraMap A (MiddleSecondOpen W c) (coord W 0 0 0 0 c 2)) = middleNodeU c := by
  have h : (middleTangentOpenEquiv W c h2).symm
      (algebraMap A (MiddleSecondOpen W c) (coord W 0 0 0 0 c 2)) =
        algebraMap A (MiddleFirstOpen W c) (coord W 0 0 0 0 c 2) := by
    apply (middleTangentOpenEquiv W c h2).injective
    rw [AlgEquiv.apply_symm_apply, middleTangentOpenEquiv_base, middleTangentEquiv_u]
  simp only [middleSecondNodeEquiv, AlgEquiv.trans_apply, h, middleFirstNodeEquiv_u]

/-- Negating the second tangent denominator does not change the original principal open. -/
theorem middle_second_open_mem (p : PrimeSpectrum A) :
    -coord W 0 0 0 0 c 1 ∉ p.asIdeal ↔ coord W 0 0 0 0 c 1 ∉ p.asIdeal := by
  rw [neg_mem_iff]

end FLT.Mazur.WeierstrassSuccessiveX
