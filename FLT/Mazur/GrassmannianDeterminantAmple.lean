/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianFiniteCoordinateCover
public import FLT.Mazur.GrassmannianDeterminantGlobalLoci

/-!
# Ampleness of the constructed Grassmannian determinant line

The finite original coordinate cover supplies compactness. The original global
determinant sections have exactly the original affine charts as generator opens,
so their degree-one sections prove ampleness of the actual glued line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
open FCurve FCurve.ModuleLineBundleTensorPullback
universe u
set_option backward.isDefEq.respectTransparency false
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}

/-- An original finite ambient basis proves ampleness of the constructed determinant line. -/
theorem determinantLine_ample (b : Module.Basis ι R M)
    (hκ : Fintype.card κ = Fintype.card ι - d) :
    AmpleLineBundle (determinantLine R M κ d) := by
  refine ⟨ambientGrassmannian_compactSpace b hκ,
    determinantLine_locallyFreeRankOne R M κ d, fun x ↦ ?_⟩
  obtain ⟨a, ha⟩ := finiteCoordinateChart_cover b hκ x
  let k := finiteCoordinateChart b hκ a
  let e : tensorPower (determinantLine R M κ d) 1 ≅ determinantLine R M κ d :=
    ModuleSheafTensor.rightUnitor _
  have he := sectionGeneratorOpen_iso e.symm (determinantGlobalSection k)
  change sectionGeneratorOpen (tensorPower (determinantLine R M κ d) 1)
    (e.inv.app ⊤ (determinantGlobalSection k)) = _ at he
  refine ⟨1, Nat.one_pos, e.inv.app ⊤ (determinantGlobalSection k), ?_, ?_⟩
  · rw [he, determinantGlobalSection_generator]
    exact ha
  · rw [he]
    exact determinantGlobalSection_generator_isAffine k

end FLT.Mazur.GrassmannianChart
