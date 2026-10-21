/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarFunctionPushout
public import FLT.Mazur.FlatAlgebraEqualizer

/-!
# Naturality of full scalar base-change coordinates

Each geometric arrow gives its own tensor square. No endpoint is recovered
from the other endpoint, and no boundary is replaced by a reduced fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.FlatScalarFunctionPushout
open SchemeScalarPrincipalNeighborhood FlatAlgebraEqualizer
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {X Y PX PY : Scheme.{0}} [Algebra R Γ(X, ⊤)] [Algebra R Γ(Y, ⊤)]

/-- An original scalar-linear arrow commutes with its structural morphisms to Spec R. -/
theorem scalarMorphism_natural (v : X ⟶ Y) (u : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤))
    (hu : u.toRingHom = v.appTop.hom) :
    v ≫ scalarMorphism (algebraMap R Γ(Y, ⊤)) =
      scalarMorphism (algebraMap R Γ(X, ⊤)) := by
  unfold scalarMorphism
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  exact (congrArg (fun f : Γ(Y, ⊤) →+* Γ(X, ⊤) ↦ f (algebraMap R Γ(Y, ⊤) r))
    hu).symm.trans (u.commutes r)

/-- Scalar sections commute with a geometric arrow over the same affine base. -/
theorem scalarMap_natural {bx : PX ⟶ Spec (.of S)} {bY : PY ⟶ Spec (.of S)}
    (v : PX ⟶ PY) (hv : v ≫ bY = bx) (s : S) :
    v.appTop (scalarMap bY s) = scalarMap bx s := by
  rw [← hv]
  simp only [scalarMap, Scheme.Hom.comp_appTop]
  rfl

variable {ax : PX ⟶ X} {bx : PX ⟶ Spec (.of S)}
  {ay : PY ⟶ Y} {bY : PY ⟶ Spec (.of S)}
  (hx : IsPullback ax bx (scalarMorphism (algebraMap R Γ(X, ⊤)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hy : IsPullback ay bY (scalarMorphism (algebraMap R Γ(Y, ⊤)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [Module.Flat R S]

/-- The tensor comparison intertwines the complete geometric coefficient maps. -/
theorem sectionsEquiv_natural (v : X ⟶ Y) (v' : PX ⟶ PY)
    (u : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤)) (hu : u.toRingHom = v.appTop.hom)
    (ha : v' ≫ ay = ax ≫ v) (hb : v' ≫ bY = bx)
    (z : S ⊗[R] Γ(Y, ⊤)) :
    sectionsEquiv hx (tensorMap S u z) = v'.appTop (sectionsEquiv hy z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s y =>
      change sectionsEquiv hx (s ⊗ₜ[R] u y) = _
      rw [sectionsEquiv_tmul, sectionsEquiv_tmul, map_mul, scalarMap_natural v' hb]
      congr 1
      have hh := congrArg (fun f : PX ⟶ Y ↦ f.appTop y) ha
      simp only [Scheme.Hom.comp_appTop] at hh
      change ax.appTop (u.toRingHom y) = _
      rw [hu]
      exact hh.symm
  | add x y ex ey => simp only [map_add, ex, ey]

end FLT.Mazur.FlatScalarFunctionPushout
