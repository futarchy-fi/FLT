/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NilpotentEtaleEquivalence
public import FLT.Mazur.OneGonTangentReductionEquivalence
public import FLT.Mazur.OneGonTangentEtaleCover
public import FLT.Mazur.OneGonNilpotentNormalForm
public import FLT.Mazur.OneGonSingularTranslation

/-!
# Independence of infinitesimal tangent-coefficient lifts

Congruent ordinary tangent quadratics have uniquely identified etale covers
before reduction. The comparison lifts the specified reduced root comparison,
so it applies to different lifts of a residual node's coordinates.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R) (I : Ideal R)
  (hI : IsNilpotent I) (hW : IsUnit W.b₂) (hV : IsUnit V.b₂)
local notation "q" => Ideal.Quotient.mk I
local notation "AW" => AdjoinRoot (nodeTangentPolynomial W)
local notation "AV" => AdjoinRoot (nodeTangentPolynomial V)
local notation "IW" => I.map (algebraMap R AW)
local notation "IV" => I.map (algebraMap R AV)

/-- The actual etale covers are equivalent before reduction, not just on the special fiber. -/
def tangentLiftEquiv (h₁ : q W.a₁ = q V.a₁) (h₂ : q W.a₂ = q V.a₂) : AW ≃ₐ[R] AV := by
  let _ := tangentAlgebra_etale W hW
  let _ := tangentAlgebra_etale V hV
  exact NilpotentEtale.liftEquiv IW IV
    (nilpotent_map I hI _) (nilpotent_map I hI _) (tangentReductionEquiv W V I h₁ h₂)

/-- The comparison keeps the specified coefficient reduction on every function. -/
theorem tangentLiftEquiv_reduction (h₁ : q W.a₁ = q V.a₁) (h₂ : q W.a₂ = q V.a₂)
    (a : AW) :
    Ideal.Quotient.mk IV (tangentLiftEquiv W V I hI hW hV h₁ h₂ a) =
      tangentReductionEquiv W V I h₁ h₂ (Ideal.Quotient.mk IW a) := by
  let _ := tangentAlgebra_etale W hW
  let _ := tangentAlgebra_etale V hV
  exact NilpotentEtale.liftEquiv_reduction IW IV
    (nilpotent_map I hI _) (nilpotent_map I hI _) _ a

/-- In particular the original residual tangent root is fixed by the cover identification. -/
theorem tangentLiftEquiv_root (h₁ : q W.a₁ = q V.a₁) (h₂ : q W.a₂ = q V.a₂)
    :
    Ideal.Quotient.mk IV (tangentLiftEquiv W V I hI hW hV h₁ h₂
      (AdjoinRoot.root (nodeTangentPolynomial W))) =
        Ideal.Quotient.mk IV (AdjoinRoot.root (nodeTangentPolynomial V)) := by
  rw [tangentLiftEquiv_reduction, tangentReductionEquiv_root]

/-- No different cover identification can have the same residual comparison. -/
theorem tangentLiftEquiv_unique (h₁ : q W.a₁ = q V.a₁) (h₂ : q W.a₂ = q V.a₂)
    (e : AW ≃ₐ[R] AV)
    (he : ∀ a, Ideal.Quotient.mk IV (e a) =
      tangentReductionEquiv W V I h₁ h₂ (Ideal.Quotient.mk IW a)) :
    e = tangentLiftEquiv W V I hI hW hV h₁ h₂ := by
  let _ := tangentAlgebra_etale W hW
  let _ := tangentAlgebra_etale V hV
  exact NilpotentEtale.liftEquiv_unique IW IV
    (nilpotent_map I hI _) (nilpotent_map I hI _) _ e he

/-- Retaining only the original residual root already determines the entire cover equivalence. -/
theorem tangentLiftEquiv_unique_root (h₁ : q W.a₁ = q V.a₁) (h₂ : q W.a₂ = q V.a₂)
    (e : AW ≃ₐ[R] AV)
    (he : Ideal.Quotient.mk IV (e (AdjoinRoot.root (nodeTangentPolynomial W))) =
      Ideal.Quotient.mk IV (AdjoinRoot.root (nodeTangentPolynomial V))) :
    e = tangentLiftEquiv W V I hI hW hV h₁ h₂ := by
  apply tangentLiftEquiv_unique
  have h : (Ideal.Quotient.mkₐ R IV).comp e.toAlgHom =
      (tangentReductionEquiv W V I h₁ h₂).toAlgHom.comp (Ideal.Quotient.mkₐ R IW) := by
    apply AdjoinRoot.algHom_ext
    change Ideal.Quotient.mk IV (e (AdjoinRoot.root (nodeTangentPolynomial W))) =
      tangentReductionEquiv W V I h₁ h₂
        (Ideal.Quotient.mk IW (AdjoinRoot.root (nodeTangentPolynomial W)))
    rw [tangentReductionEquiv_root]
    exact he
  exact fun a => AlgHom.congr_fun h a

/-- Different lifts of the same residual node give equivalent original etale tangent covers. -/
def centeredTangentLiftEquiv (x y x' y' : R)
    (hx : q x = q x') (hy : q y = q y')
    (hd : IsUnit (q (W.b₂ + 12 * x))) :
    AdjoinRoot (nodeTangentPolynomial (centeredEquation W x y)) ≃ₐ[R]
      AdjoinRoot (nodeTangentPolynomial (centeredEquation W x' y')) := by
  have he : (centeredEquation W x y).map q = (centeredEquation W x' y').map q := by
    rw [centeredEquation_map, centeredEquation_map, hx, hy]
  have hb : IsUnit (centeredEquation W x y).b₂ := by
    rw [centeredEquation_b₂]
    exact hI.isUnit_quotient_mk_iff.mp hd
  have hb' : IsUnit (centeredEquation W x' y').b₂ := by
    apply hI.isUnit_quotient_mk_iff.mp
    simpa only [centeredEquation_b₂, map_add, map_mul, map_ofNat, hx] using hd
  exact tangentLiftEquiv _ _ I hI hb hb'
    (congrArg WeierstrassCurve.a₁ he) (congrArg WeierstrassCurve.a₂ he)

end FLT.Mazur.OneGonInfinitesimal
