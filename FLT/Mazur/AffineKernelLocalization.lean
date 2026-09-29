/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CoherentSubquotient

/-!
# Affine kernels from actual global sections

The ambient sheaf kernel is tilde of the kernel of the actual global-section
map. The counit comparisons identify the inclusions. No Noetherian or finite
presentation assumption is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

variable {R : CommRingCat.{u}} {M N : (Spec R).Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)

/-- The kernel in the ambient sheaf category is tilde of the global-section kernel. -/
def affineKernelIso : tilde (kernel (moduleSpecΓFunctor.map f)) ≅ kernel f :=
  PreservesKernel.iso (tilde.functor R) (moduleSpecΓFunctor.map f) ≪≫
    kernel.mapIso _ f (asIso M.fromTildeΓ) (asIso N.fromTildeΓ)
      (Scheme.Modules.fromTildeΓNatTrans.naturality f)

/-- The comparison identifies the actual kernel inclusions through the counit. -/
@[reassoc (attr := simp)]
lemma affineKernelIso_hom_ι :
    (affineKernelIso f).hom ≫ kernel.ι f =
      (tilde.functor R).map (kernel.ι (moduleSpecΓFunctor.map f)) ≫ M.fromTildeΓ := by
  simp only [affineKernelIso, Iso.trans_hom, PreservesKernel.iso_hom,
    kernel.mapIso_hom, kernel.map, Category.assoc, kernel.lift_ι, asIso_hom]
  rw [← Category.assoc, kernelComparison_comp_ι]

/-- The kernel identification is natural in a commutative square of sheaf maps. -/
lemma affineKernelIso_naturality {M' N' : (Spec R).Modules}
    [M'.IsQuasicoherent] [N'.IsQuasicoherent] (f' : M' ⟶ N')
    (a : M ⟶ M') (b : N ⟶ N') (h : f ≫ b = a ≫ f') :
    (tilde.functor R).map
        (kernel.map (moduleSpecΓFunctor.map f) (moduleSpecΓFunctor.map f')
          (moduleSpecΓFunctor.map a) (moduleSpecΓFunctor.map b) (by
            simpa only [Functor.map_comp] using congrArg moduleSpecΓFunctor.map h)) ≫
        (affineKernelIso f').hom =
      (affineKernelIso f).hom ≫ kernel.map f f' a b h := by
  apply (cancel_mono (kernel.ι f')).mp
  simp only [Category.assoc, affineKernelIso_hom_ι, kernel.map, kernel.lift_ι]
  rw [← Category.assoc, ← Functor.map_comp, kernel.lift_ι, Functor.map_comp]
  rw [Category.assoc]
  erw [Scheme.Modules.fromTildeΓNatTrans.naturality a]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ a) (affineKernelIso_hom_ι f)).symm.trans
      (Category.assoc _ _ _))

end FLT.Mazur.FCurve
