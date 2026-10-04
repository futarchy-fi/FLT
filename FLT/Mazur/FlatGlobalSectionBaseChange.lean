/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatCartesianSectionGluing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat base change of global sections

For a quasi-compact separated scheme over an affine base, quasi-coherent global
sections commute with flat affine base change. The isomorphism is the canonical
map obtained from the sheaf pullback adjunction unit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings
namespace FLT.Mazur.FlatGlobalSectionBaseChange
open OpenModuleSectionScalars CartesianOpenSectionMap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]

/-- The canonical global comparison is invertible for flat affine base change. -/
instance comparison_isIso : IsIso (comparison h M ⊤) := by
  classical
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.Opens := fun i ↦ (C.f i).opensRange
  have hA (i : C.I₀) : IsAffineOpen (U i) := isAffineOpen_opensRange (C.f i)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact FlatCartesianSectionGluing.comparison_bijective h M U C.iSup_opensRange hA
    (fun i j ↦ (hA i).inf (hA j)) g.flat_appTop

/-- Global sections after flat affine base change, with the original base scalars. -/
def sectionsIso :
    (ModuleCat.extendScalars g.appTop.hom).obj (openSections f M ⊤) ≅
      openSections q ((pullback p).obj M) ⊤ :=
  asIso (comparison h M ⊤)

/-- The global comparison sends a pure tensor to the scaled pullback unit. -/
lemma sectionsIso_tmul (b : Γ(T, ⊤)) (m : openSections f M ⊤) :
    (sectionsIso h M).hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m) =
      b • (show openSections q ((pullback p).obj M) ⊤ from
        ((pullbackPushforwardAdjunction p).unit.app M).app ⊤ m) :=
  comparison_tmul h M ⊤ b m

/-- Restricting the global comparison yields the canonical comparison on every open. -/
lemma sectionsIso_restrict (U : X.Opens) :
    (sectionsIso h M).hom ≫ ModuleCat.ofHom
        (X := openSections q ((pullback p).obj M) ⊤)
        (Y := openSections q ((pullback p).obj M) (p ⁻¹ᵁ U))
        (Chow.baseRestriction ((pullback p).obj M) q.appTop.hom le_top) =
      (ModuleCat.extendScalars g.appTop.hom).map
        (ModuleCat.ofHom (Chow.baseRestriction M f.appTop.hom (show U ≤ ⊤ from le_top))) ≫
          comparison h M U :=
  (CartesianSectionRestriction.comparison_naturality h M le_top).symm

end FLT.Mazur.FlatGlobalSectionBaseChange
