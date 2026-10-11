/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeUnpointedFppfAcyclicOpen
public import FLT.Mazur.UnpointedLocalAcyclicFppfSheaf

/-!
# Arbitrary base change for unpointed Picard-sheaf acyclic opens

The descended open commutes with every test morphism. It is the whole test
exactly when the actual section belongs to the local acyclic subsheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- Every test morphism pulls back the actual descended open of an arbitrary sheaf section. -/
theorem finiteTypeUnpointedFppfAcyclicOpen_map
    {T U : Over (Spec (.of R))} (b : U ⟶ T)
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    finiteTypeUnpointedFppfAcyclicOpen f U ((relativeFppfSheaf f).obj.map b.op s) =
      b.left ⁻¹ᵁ finiteTypeUnpointedFppfAcyclicOpen f T s := by
  obtain ⟨𝒰, h𝒰⟩ := relativeFppfClass_exists_cover f U
    ((relativeFppfSheaf f).obj.map b.op s)
  apply SchemeFppfOpen.ext 𝒰
  intro i
  obtain ⟨c, hc⟩ := h𝒰 i
  have hcomp : relativeFppfClass f _ c = (relativeFppfSheaf f).obj.map
      ((relativeCoverArrow U 𝒰 i) ≫ b).op s := by
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hc
  exact (finiteTypeUnpointedFppfAcyclicOpen_representative f U _
    (relativeCoverArrow U 𝒰 i) c hc).trans
      (finiteTypeUnpointedFppfAcyclicOpen_representative f T s
        ((relativeCoverArrow U 𝒰 i) ≫ b) c hcomp).symm

/-- The actual descended open is the whole test precisely for locally acyclic sections. -/
theorem finiteTypeUnpointedFppfAcyclicOpen_eq_top (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    finiteTypeUnpointedFppfAcyclicOpen f T s = ⊤ ↔
      s ∈ (localGeometricAcyclicFppfSubfunctor f).obj (op T) := by
  obtain ⟨𝒰, h𝒰⟩ := relativeFppfClass_exists_cover f T s
  constructor
  · intro htop
    apply localGeometricAcyclicFppf_of_cover f T s 𝒰
    intro i
    obtain ⟨c, hc⟩ := h𝒰 i
    refine ⟨c, ?_, hc⟩
    apply (finiteTypeRelativeClassOpen_eq_top f _ c).mp
    rw [← finiteTypeUnpointedFppfAcyclicOpen_representative f T s
      (relativeCoverArrow T 𝒰 i) c hc, htop]
    rfl
  · intro hs
    apply SchemeFppfOpen.ext 𝒰
    intro i
    obtain ⟨c, hc⟩ := h𝒰 i
    refine (finiteTypeUnpointedFppfAcyclicOpen_representative f T s
      (relativeCoverArrow T 𝒰 i) c hc).trans ?_
    apply (finiteTypeRelativeClassOpen_eq_top f _ c).mpr
    apply (localGeometricAcyclicFppf_class_iff f _ c).mp
    rw [hc]
    exact (localGeometricAcyclicFppfSubfunctor f).map
      (relativeCoverArrow T 𝒰 i).op hs

end FLT.Mazur.CartierAbel
