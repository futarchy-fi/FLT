/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffinePairDescent
public import FLT.Mazur.WeierstrassAffineInputTripleGlobal

/-!
# Descent of associativity from the four affine-input addition domains

Pulling back the genuine four-chart cover for each pair removes every choice
of secant or tangent denominator. The remaining geometric hypotheses are only
that both original pairs and both intermediate pairs have affine inputs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Associativity descends to any scheme carrying affine presentations of the four pairs. -/
theorem integralCurveTripleAdd_of_affinePairs {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W)
    (a b c d : X ⟶ Spec (.of (AffineProduct W)))
    (ha : a ≫ integralCurveProductChart W false false = t ≫ integralCurveTriplePair W)
    (hb : b ≫ integralCurveProductChart W false false = t ≫ integralCurveTripleLastPair W)
    (hc : c ≫ integralCurveProductChart W false false = t ≫ integralCurveAddFirstPair W hΔ)
    (hd : d ≫ integralCurveProductChart W false false = t ≫ integralCurveAddLastPair W hΔ) :
    t ≫ integralCurveTripleAddLeft W hΔ = t ≫ integralCurveTripleAddRight W hΔ := by
  apply affinePair_hom_ext W hΔ a
  intro i X₁ u f hf
  have hf' : f ≫ additionGlobalDomain W i = u ≫ t ≫ integralCurveTriplePair W := by
    rw [additionGlobalDomain, ← Category.assoc, hf, Category.assoc, ha]
  apply affinePair_hom_ext W hΔ (u ≫ b)
  intro j X₂ v g hg
  have hg' : g ≫ additionGlobalDomain W j =
      v ≫ u ≫ t ≫ integralCurveTripleLastPair W := by
    calc
      _ = (v ≫ u ≫ b) ≫ integralCurveProductChart W false false :=
        congrArg (fun e => e ≫ integralCurveProductChart W false false) hg
      _ = _ := by simp only [Category.assoc, hb]
  apply affinePair_hom_ext W hΔ (v ≫ u ≫ c)
  intro k X₃ w h hh
  have hh' : h ≫ additionGlobalDomain W k =
      w ≫ v ≫ u ≫ t ≫ integralCurveAddFirstPair W hΔ := by
    calc
      _ = (w ≫ v ≫ u ≫ c) ≫ integralCurveProductChart W false false :=
        congrArg (fun e => e ≫ integralCurveProductChart W false false) hh
      _ = _ := by simp only [Category.assoc, hc]
  apply affinePair_hom_ext W hΔ (w ≫ v ≫ u ≫ d)
  intro l X₄ x q hq
  have hq' : q ≫ additionGlobalDomain W l =
      x ≫ w ≫ v ≫ u ≫ t ≫ integralCurveAddLastPair W hΔ := by
    calc
      _ = (x ≫ w ≫ v ≫ u ≫ d) ≫ integralCurveProductChart W false false :=
        congrArg (fun e => e ≫ integralCurveProductChart W false false) hq
      _ = _ := by simp only [Category.assoc, hd]
  have he := integralCurveTripleAdd_affineInputs W hΔ (x ≫ w ≫ v ≫ u ≫ t) i j k l
    (x ≫ w ≫ v ≫ f) (x ≫ w ≫ g) (x ≫ h) q
    (by simp only [Category.assoc, hf']) (by simp only [Category.assoc, hg'])
    (by simp only [Category.assoc, hh']) (by simpa only [Category.assoc] using hq')
  simpa only [Category.assoc] using he

end FLT.Mazur.WeierstrassIntegralChart
