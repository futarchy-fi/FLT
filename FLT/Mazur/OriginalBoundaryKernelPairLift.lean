/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryBranchScalars

/-!
# Construct full branch boundary lifts by kernel-pair descent

An effective epimorphic full boundary over a quotient of the scalar base admits descent
when its entire kernel pair is dominated by original boundary relation arrows.
The original compatibility equation supplies the branch equation; no scalar
solution or full branch numerator is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FlatScalarFunctionPushout

/-- A scalar quotient factorization keeps the literal scalar function on the full scheme. -/
theorem scalarMap_factor {S T : Type} [CommRing S] [CommRing T] {X : Scheme.{0}}
    (c : X ⟶ Spec (.of T)) (b : X ⟶ Spec (.of S)) (ρ : S →+* T)
    (hc : c ≫ Spec.map (CommRingCat.ofHom ρ) = b) (s : S) :
    scalarMap b s = scalarMap c (ρ s) := by
  rw [← hc]
  unfold scalarMap
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end FLT.Mazur.FlatScalarFunctionPushout

namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections RingPairInvariantFlatScalars
open FlatScalarSchemeBaseChange FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} (p q : D ⟶ A)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] FlatScalarSchemeBaseChange.baseChange
variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
variable {T : Type} [CommRing T] (ρ : S →+* T) (hρ : Function.Surjective ρ)
  (c : baseChange (invariants p.appTop.hom q.appTop.hom) S J.subscheme ⟶ Spec (.of T))
  [EffectiveEpi c]
  (hc : c ≫ Spec.map (CommRingCat.ofHom ρ) =
    base (invariants p.appTop.hom q.appTop.hom) S J.subscheme)

include hρ hc in
/-- Full kernel-pair domination constructs the scalar boundary equation from original invariance. -/
theorem originalBoundary_scalar_of_kernelPair_cover
    {E : Scheme.{0}} (k : E ⟶ pullback c c) [Epi k]
    (u : E ⟶ pullback p J.subschemeι)
    (ha : k ≫ pullback.fst c c ≫ source R S J.subscheme = u ≫ pullback.snd p J.subschemeι)
    (hb : k ≫ pullback.snd c c ≫ source R S J.subscheme =
      u ≫ InvariantIdealRelation.snd J p q hJ)
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ s : S, FlatScalarFunctionPushout.scalarMap (base R S J.subscheme) s =
      (source R S J.subscheme).appTop t.val := by
  have he : (pullback.fst c c).appTop ((source R S J.subscheme).appTop t.val) =
      (pullback.snd c c).appTop ((source R S J.subscheme).appTop t.val) := by
    apply appTop_injective k
    have h₁ := congrArg (fun f : E ⟶ J.subscheme ↦ f.appTop t.val) ha
    have h₂ := congrArg (fun f : E ⟶ J.subscheme ↦ f.appTop t.val) hb
    simp only [Scheme.Hom.comp_appTop] at h₁ h₂
    exact h₁.trans ((congrArg u.appTop t.property).trans h₂.symm)
  obtain ⟨v, hv, _⟩ := sections_existsUnique (IsPullback.of_hasPullback c c)
    ((source R S J.subscheme).appTop t.val) he
  let e := (Scheme.ΓSpecIso (.of T)).commRingCatIsoToRingEquiv
  obtain ⟨s, hs⟩ := hρ (e v)
  refine ⟨s, ?_⟩
  have hm : FlatScalarFunctionPushout.scalarMap (base R S J.subscheme) s =
      FlatScalarFunctionPushout.scalarMap c (ρ s) := scalarMap_factor c _ ρ hc s
  rw [hm, hs]
  change c.appTop (e.symm (e v)) = _
  rw [e.symm_apply_apply, hv]

include hρ hc in
/-- Kernel-pair descent constructs an actual full invariant branch numerator. -/
theorem originalBoundary_geometric_lift_of_kernelPair_cover
    {E : Scheme.{0}} (k : E ⟶ pullback c c) [Epi k]
    (u : E ⟶ pullback p J.subschemeι)
    (ha : k ≫ pullback.fst c c ≫ source R S J.subscheme = u ≫ pullback.snd p J.subschemeι)
    (hb : k ≫ pullback.snd c c ≫ source R S J.subscheme =
      u ≫ InvariantIdealRelation.snd J p q hJ)
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ a : Γ(baseChange R S A, ⊤),
      (originalBranchFirst p q S).appTop a = (originalBranchSecond p q S).appTop a ∧
      (originalBranchBoundary p q J S).appTop a = (source R S J.subscheme).appTop t.val := by
  obtain ⟨s, hs⟩ := originalBoundary_scalar_of_kernelPair_cover p q J hJ S ρ hρ c hc k u ha hb t
  exact originalBranch_lift_of_scalar p q S J t.val s hs

end FLT.Mazur.EquivalenceRelationOrderedFrames
