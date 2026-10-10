/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafSectionRigidity
public import FLT.Mazur.ProperSmoothStructureSheaf

/-!
# Rigidity of pointed proper smooth line bundles

For proper smooth geometrically connected pointed families, actual line
endomorphisms are unique base scalars. Every rigidified automorphism is trivial,
including on every cartesian base change, over unrestricted original bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProperSmoothLineRigidity
open FCurve FCurve.ModuleSheafScalarEndomorphisms IdealPowerScalarLift
variable {X S : Scheme.{0}} (f : X ⟶ S)
  [IsProper f] [Smooth f] [GeometricallyConnected f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include s hs
/-- Every line endomorphism is multiplication by a unique function on the original base. -/
theorem existsUnique_baseScalar {M : X.Modules} (hM : LocallyFreeRankOne M) (φ : M ⟶ M) :
    ∃! r : Γ(S, ⊤), scalarEnd M (f.appTop r) = φ := by
  have hb := (scalarEnd_bijective hM).comp
    (ProperSmoothStructureSheaf.appTop_bijective f s hs)
  obtain ⟨r, hr⟩ := hb.surjective φ
  exact ⟨r, hr, fun t ht ↦ hb.injective (ht.trans hr.symm)⟩

/-- Pullback to the chosen section is faithful on actual line endomorphisms. -/
theorem pullback_end_injective {M : X.Modules} (hM : LocallyFreeRankOne M) :
    Function.Injective (fun φ : M ⟶ M ↦ (pullback s).map φ) :=
  LineSheafSectionRigidity.pullback_end_injective f s hs
    (ProperSmoothStructureSheaf.appTop_bijective f s hs).surjective hM

/-- Actual rigidified automorphisms are trivial without restrictions on the original base. -/
theorem rigidified_auto_eq_refl {M : X.Modules} (hM : LocallyFreeRankOne M)
    (ρ : (pullback s).obj M ≅ structureModule S) (e : M ≅ M)
    (he : (pullback s).map e.hom ≫ ρ.hom = ρ.hom) : e = Iso.refl M :=
  LineSheafSectionRigidity.rigidified_auto_eq_refl f s hs
    (ProperSmoothStructureSheaf.appTop_bijective f s hs).surjective hM ρ e he

/-- The same rigidity holds for every line on every cartesian base change. -/
theorem cartesian_rigidified_auto_eq_refl {P T : Scheme.{0}}
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g)
    {M : P.Modules} (hM : LocallyFreeRankOne M)
    (ρ : (pullback (ArtinianProperAffineBaseChange.sectionOfSquare h s hs)).obj M ≅
      structureModule T) (e : M ≅ M)
    (he : (pullback (ArtinianProperAffineBaseChange.sectionOfSquare h s hs)).map e.hom ≫
      ρ.hom = ρ.hom) : e = Iso.refl M := by
  let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
  let _ : Smooth q := MorphismProperty.of_isPullback h inferInstance
  let _ : GeometricallyConnected q := MorphismProperty.of_isPullback h inferInstance
  exact rigidified_auto_eq_refl q (ArtinianProperAffineBaseChange.sectionOfSquare h s hs)
    (ArtinianProperAffineBaseChange.sectionOfSquare_projection h s hs) hM ρ e he

end FLT.Mazur.ProperSmoothLineRigidity
