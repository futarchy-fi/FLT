/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveCoordinateGeneratorOpen
public import FLT.Mazur.RelativeAmpleProper

/-!
# Affine generator opens from closed projective presentations

Pulling back the homogeneous coordinates along a closed immersion gives
actual sections of the presented line bundle with affine generator opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace.VeryAmplePresentation
attribute [local instance] MvPolynomial.gradedAlgebra
variable {A : Type} [CommRing A] {X : Scheme} {f : X ⟶ Spec (.of A)}
  {L : X.Modules} (p : VeryAmplePresentation f L)

include p in
/-- The coordinate sections of a closed presentation have affine generator opens. -/
theorem exists_affine_generator_section (x : X) :
    ∃ s : Γ(L, ⊤), x ∈ sectionGeneratorOpen L s ∧ IsAffineOpen (sectionGeneratorOpen L s) := by
  obtain ⟨i, hi⟩ := exists_mem_chart A (Fin (p.dimension + 1)) (p.embedding x)
  let t : Γ(O A p.dimension 1, ⊤) := coordinateGlobalSection A (Fin (p.dimension + 1)) i
  let s := p.coefficientIso.inv.app ⊤ (pullGlobal p.embedding (O A p.dimension 1) t)
  have he : sectionGeneratorOpen L s = p.embedding ⁻¹ᵁ chart A (Fin (p.dimension + 1)) i := by
    exact (sectionGeneratorOpen_iso p.coefficientIso.symm _).trans
      ((sectionGeneratorOpen_pullGlobal (O_locallyFreeRankOne A p.dimension 1) p.embedding t).trans
        (congrArg (p.embedding ⁻¹ᵁ ·)
          (coordinateGlobalSection_generatorOpen A (Fin (p.dimension + 1)) i)))
  refine ⟨s, he ▸ hi, he ▸ ?_⟩
  exact (Proj.isAffineOpen_basicOpen (grading A (Fin (p.dimension + 1))) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X A i) (by decide)).preimage p.embedding

include p in
/-- Every closed projective presentation is ample in the affine-section sense. -/
theorem ampleLineBundle : AmpleLineBundle L := by
  let := p.isProper
  refine ⟨QuasiCompact.compactSpace_of_compactSpace f, p.locallyFreeRankOne, fun x ↦ ?_⟩
  obtain ⟨s, hx, hs⟩ := p.exists_affine_generator_section x
  let e : L ≅ ModuleLineBundleTensorPullback.tensorPower L 1 :=
    (ModuleSheafTensor.rightUnitor L).symm
  refine ⟨1, by decide, e.hom.app ⊤ s, ?_, ?_⟩
  · simpa only [sectionGeneratorOpen_iso] using hx
  · simpa only [sectionGeneratorOpen_iso] using hs

end FLT.Mazur.ProjectiveSpace.VeryAmplePresentation
