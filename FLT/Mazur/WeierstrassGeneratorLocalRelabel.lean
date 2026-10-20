/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorTorsionLocalRelabel
public import FLT.Mazur.GroupTorsionUnramifiedBaseChange
public import FLT.Mazur.WeierstrassGeneralizedEllipticModel
public import FLT.Mazur.WeierstrassTorsionFormallyUnramified

/-!
# Actual Weierstrass Cartier generators match locally at invertible levels

The original compatible family comparison and every generator power are
retained. The coefficient base has invertible level; the subsequent scheme
base change is arbitrary and may have nilpotents. No etaleness of the finite
subgroup is an input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.WeierstrassIntegralChart
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
  {T : Scheme} (g : T ⟶ Spec (.of R))

/-- Ambient infinitesimal torsion rigidity survives arbitrary base change of the actual model. -/
theorem generalizedTorsion_baseChange_formallyUnramified (n : ℕ) (hn : IsUnit (n : R)) :
    FormallyUnramified (GroupTorsionScheme.scheme
      ((integralGeneralizedEllipticCurve W hΔ).baseChange g).group n).hom := by
  let _ := integralTorsion_formallyUnramified W hΔ n hn
  exact GroupTorsionScheme.baseChange_formallyUnramified g (integralCurveGroup W hΔ).X n

variable {n : ℕ} [NeZero n] (hn : IsUnit (n : R))
  (J : ((integralGeneralizedEllipticCurve W hΔ).baseChange g).FiniteSubgroup n)

include hn

/-- Invertible level gives a local full-level relabeling of actual Cartier generators. -/
theorem cartierGenerator_local_relabel
    {P Q : 𝟙_ (Over T) ⟶ J.carrier}
    (hP : J.IsCartierGenerator P) (hQ : J.IsCartierGenerator Q) (x : T) :
    ∃ (r : MulAut (Multiplicative (ZMod n))) (U : T.Opens),
      IsAffineOpen U ∧ x ∈ U ∧ ∀ i,
        U.ι ≫ (P ^ (r i).toAdd.val).left = U.ι ≫ (Q ^ i.toAdd.val).left := by
  let _ : IsSeparated ((integralGeneralizedEllipticCurve W hΔ).baseChange g).group.hom := by
    change IsSeparated (pullback.snd (integralCurveStructure W) g)
    infer_instance
  let _ : LocallyOfFiniteType ((integralGeneralizedEllipticCurve W hΔ).baseChange g).group.hom := by
    change LocallyOfFiniteType (pullback.snd (integralCurveStructure W) g)
    infer_instance
  let _ := generalizedTorsion_baseChange_formallyUnramified W hΔ g n hn
  exact hP.exists_local_relabel_of_torsion J hQ x

/-- Every original compatible comparison matches all cyclic labels locally at invertible level. -/
theorem compatibleIso_local_generator_relabel
    {F : GeneralizedEllipticCurve T} {H : F.FiniteSubgroup n} (a : CompatibleIso H J)
    {P : 𝟙_ (Over T) ⟶ H.carrier} {Q : 𝟙_ (Over T) ⟶ J.carrier}
    (hP : H.IsCartierGenerator P) (hQ : J.IsCartierGenerator Q) (x : T) :
    ∃ (r : MulAut (Multiplicative (ZMod n))) (U : T.Opens),
      IsAffineOpen U ∧ x ∈ U ∧ ∀ i,
        U.ι ≫ (P ^ (r i).toAdd.val).left ≫ a.subgroup.hom.left =
          U.ι ≫ (Q ^ i.toAdd.val).left := by
  obtain ⟨r, U, hU, hx, he⟩ :=
    cartierGenerator_local_relabel W hΔ g hn J (a.cartierGenerator hP) hQ x
  refine ⟨r, U, hU, hx, fun i => ?_⟩
  simpa only [← pow_comp, Over.comp_left] using he i

end FLT.Mazur.WeierstrassIntegralChart
