/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealModulePullbackRestrict
public import FLT.Mazur.ModuleSheafOpenIsoDetection
public import FLT.Mazur.PolygonDivisorNormalizationPullback
/-!
# The actual ideal-module comparison on polygon normalization

Normalization is unchanged over the torus. At the endpoints the boundary
divisor has empty support, so the unit-ideal comparison applies. This includes
the one-gon and both nodes of the two-gon.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
universe u
namespace FLT.Mazur.PolygonIdealModulePullback
open PolygonPinching PolygonMarkedSections FCurve
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- The boundary divisor misses every node. -/
lemma node_not_support (a : Fin n → Kˣ) (i : Fin n) (x : Spec (.of K)) :
    (nodeι K n i ≫ q).left x ∉ (PolygonBoundaryDivisor.ideal K n p a).support := by
  intro hx
  obtain ⟨j, z, hz⟩ := (PolygonBoundaryDivisor.mem_support_iff K n p hn q h a _).mp hx
  exact PolygonNormalizationTorusPullback.node_not_torus K n hn p q h j i x
    (hz ▸ section_mem_torus K n p (a j) j z)

include h in
/-- The component torus and the inverse image of the divisor complement cover P1. -/
lemma cover (a : Fin n → Kˣ) (i : Fin n) (z : ProjectiveLine.scheme K) :
    z ∈ (torusToComponent K).left.opensRange ∨
      z ∈ (componentι K n i ≫ p).left ⁻¹ᵁ
        (PolygonBoundaryDivisor.ideal K n p a).support.compl := by
  rcases ProjectiveLine.torus_or_endpoints K z with ht | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact Or.inl ht
  · right
    have he := congrArg (fun f ↦ f.left x)
      (PolygonNodeIncidence.zero_node K n hn p q h i)
    change (componentι K n i ≫ p).left _ ∉ _
    intro hz
    exact node_not_support K n hn p q h a i x (he ▸ hz)
  · right
    let j := (finRotate n).symm i
    have hj : next hn j = i := by
      rw [PolygonCyclicAtlas.next_eq_rotate, Equiv.apply_symm_apply]
    have he := congrArg (fun f ↦ f.left x)
      (PolygonNodeIncidence.infinity_node K n hn p q h j)
    rw [hj] at he
    change (componentι K n i ≫ p).left _ ∉ _
    intro hz
    exact node_not_support K n hn p q h a j x (he ▸ hz)

include h in
/-- The canonical module comparison is invertible on each normalization component. -/
theorem comparison_isIso (a : Fin n → Kˣ) (i : Fin n) :
    IsIso (idealModulePullbackHom (PolygonBoundaryDivisor.ideal K n p a)
      (componentι K n i ≫ p).left) := by
  let I := PolygonBoundaryDivisor.ideal K n p a
  let f := (componentι K n i ≫ p).left
  let t := (torusToComponent K).left
  let j := (torusToComponent K ≫ componentι K n i ≫ p).left
  let := torus_isOpenImmersion K n hn p q h i
  have ht : IsIso ((Scheme.Modules.restrictFunctor t).map (idealModulePullbackHom I f)) :=
    idealModulePullbackHom_isIso_restrict I f (𝟙 _) t j (by simp [f, t, j])
  have hr := moduleHom_isIso_restrict_opensRange (idealModulePullbackHom I f) t
  have hc := idealModulePullbackHom_offSupport I f
  let U : Bool → (ProjectiveLine.scheme K).Opens :=
    fun b ↦ if b then f ⁻¹ᵁ I.support.compl else t.opensRange
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover (idealModulePullbackHom I f) U
  · intro z
    rcases cover K n hn p q h a i z with hz | hz
    · exact ⟨false, hz⟩
    · exact ⟨true, hz⟩
  · intro b
    cases b
    · exact hr
    · exact hc

/-- Pullback of the polygon ideal module is the marked-point ideal module. -/
def idealIso (a : Fin n → Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).obj
      (idealModule (PolygonBoundaryDivisor.ideal K n p a)) ≅
        idealModule (PolygonDivisorNormalizationPullback.markedPoint K (a i)).ker := by
  letI := comparison_isIso K n hn p q h a i
  exact idealModulePullbackIsoOfEq (PolygonBoundaryDivisor.ideal K n p a)
    (componentι K n i ≫ p).left _
      (PolygonDivisorNormalizationPullback.ideal K n hn p q h a i)

/-- The normalization comparison preserves the actual ideal inclusion. -/
@[reassoc]
lemma idealIso_ι (a : Fin n → Kˣ) (i : Fin n) :
    (idealIso K n hn p q h a i).hom ≫
      idealModuleι (PolygonDivisorNormalizationPullback.markedPoint K (a i)).ker =
        idealModulePullbackι (PolygonBoundaryDivisor.ideal K n p a)
          (componentι K n i ≫ p).left := by
  let := comparison_isIso K n hn p q h a i
  exact idealModulePullbackIsoOfEq_ι (PolygonBoundaryDivisor.ideal K n p a)
    (componentι K n i ≫ p).left _
      (PolygonDivisorNormalizationPullback.ideal K n hn p q h a i)

end FLT.Mazur.PolygonIdealModulePullback
