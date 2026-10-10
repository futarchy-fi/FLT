/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianSectionRestriction
public import FLT.Mazur.ModulePullbackUnitCoherence

/-!
# Cartesian comparison for actual structure sections

The affine-chart comparison, followed by the structure-module pullback
isomorphism, identifies scalar-extended functions with actual functions on
the inverse-image open. No flatness of the change of base is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings
namespace FLT.Mazur.CartesianStructureSections
open Chow OpenModuleSectionScalars FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g)

/-- The comparison to actual functions, with their original structural scalars. -/
def comparison (U : X.Opens) :
    (ModuleCat.extendScalars g.appTop.hom).obj (openSections f (structureModule X) U) ⟶
      openSections q (structureModule P) (p ⁻¹ᵁ U) :=
  CartesianOpenSectionMap.comparison h (structureModule X) U ≫
    (ModuleCat.restrictScalars
      ((P.presheaf.map (p ⁻¹ᵁ U).leTop.op).hom.comp q.appTop.hom)).map
        ((FCurve.modulePullbackUnitIso p).hom.val.app (op (p ⁻¹ᵁ U)))

/-- A pure tensor is the original pulled-back function times its base coefficient. -/
lemma comparison_tmul (U : X.Opens) (b : Γ(T, ⊤)) (m : Γ(X, U)) :
    comparison h U (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m) =
      P.presheaf.map (p ⁻¹ᵁ U).leTop.op (q.appTop b) * p.app U m := by
  change (FCurve.modulePullbackUnitIso p).hom.app (p ⁻¹ᵁ U)
    (CartesianOpenSectionMap.comparison h (structureModule X) U
      (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m)) = _
  rw [CartesianOpenSectionMap.comparison_tmul]
  change (FCurve.modulePullbackUnitIso p).hom.app (p ⁻¹ᵁ U)
    (P.presheaf.map (p ⁻¹ᵁ U).leTop.op (q.appTop b) • _) = _
  rw [Hom.app_smul, FCurve.modulePullbackUnitIso_unit]
  rfl

/-- Affine charts give a bijection even for nonflat changes of base. -/
lemma comparison_bijective [IsAffine T] [IsAffine S]
    (U : X.Opens) (hU : IsAffineOpen U) : Function.Bijective (comparison h U) := by
  let _ : (structureModule X).IsFinitePresentation := unitSheaf_isFinitePresentation X
  let _ := CartesianOpenSectionMap.comparison_isIso h (structureModule X) U hU
  exact (ConcreteCategory.bijective_of_isIso
    ((modulePullbackUnitIso p).hom.app (p ⁻¹ᵁ U))).comp
      (ConcreteCategory.bijective_of_isIso
        (CartesianOpenSectionMap.comparison h (structureModule X) U))

/-- Comparison commutes with the original restriction maps on pure tensors. -/
lemma comparison_restrict {U V : X.Opens} (i : U ≤ V)
    (b : Γ(T, ⊤)) (m : Γ(X, V)) :
    baseRestriction (structureModule P) q.appTop.hom
        ((TopologicalSpace.Opens.map p.base).map (homOfLE i)).le
        (comparison h V (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m)) =
      comparison h U (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom]
        (baseRestriction (structureModule X) f.appTop.hom i m)) := by
  rw [comparison_tmul, comparison_tmul]
  change P.presheaf.map _ (_ * _) = _ * _
  rw [map_mul]
  congr 1
  · rw [← Functor.map_comp_apply]
    rfl
  · exact congrArg (fun k ↦ k m) (p.naturality (homOfLE i).op).symm

end FLT.Mazur.CartesianStructureSections
