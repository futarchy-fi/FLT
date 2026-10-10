/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatSubschemeQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Full quotient algebras on arbitrary affine opens of closed families

An affine open need not contain the entire closed family. Flatness,
quasi-finiteness and algebra finite presentation still follow from the actual
family morphism, through its section isomorphism with the full ideal quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData)
variable (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1)

/-- The closed-family section map is the actual chart quotient's coefficient map. -/
theorem open_subscheme_quotient_structureMap :
    let _ := (f.appLE U V e).hom.toAlgebra
    (I.subschemeObjIso V).hom.hom.comp
      ((I.subschemeι ≫ f).appLE U (I.subschemeι ⁻¹ᵁ V.1)
        ((Opens.map I.subschemeι.base).monotone e)).hom =
      algebraMap Γ(Y, U) (Γ(X, V) ⧸ I.ideal V) := by
  let _ := (f.appLE U V e).hom.toAlgebra
  change (((I.subschemeι ≫ f).appLE U (I.subschemeι ⁻¹ᵁ V.1) _) ≫
    (I.subschemeObjIso V).hom).hom = _
  rw [← Scheme.Hom.appLE_comp_appLE I.subschemeι f U V
    (I.subschemeι ⁻¹ᵁ V.1) e le_rfl, ← Scheme.Hom.app_eq_appLE,
    I.subschemeι_app V, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Flatness survives restriction to an arbitrary affine ambient chart. -/
theorem flat_open_subscheme_ideal_quotient [Flat (I.subschemeι ≫ f)] :
    let _ := (f.appLE U V e).hom.toAlgebra
    Module.Flat Γ(Y, U) (Γ(X, V) ⧸ I.ideal V) := by
  let _ := (f.appLE U V e).hom.toAlgebra
  rw [← RingHom.flat_algebraMap_iff, ← open_subscheme_quotient_structureMap f I U V e]
  exact RingHom.Flat.comp
    ((I.subschemeι ≫ f).flat_appLE U.2 (V.2.preimage I.subschemeι) _)
    (.of_bijective (I.subschemeObjIso V).commRingCatIsoToRingEquiv.bijective)

/-- Arbitrary affine restrictions of a quasi-finite family have quasi-finite full quotients. -/
theorem quasiFinite_open_subscheme_ideal_quotient [LocallyQuasiFinite (I.subschemeι ≫ f)] :
    let _ := (f.appLE U V e).hom.toAlgebra
    Algebra.QuasiFinite Γ(Y, U) (Γ(X, V) ⧸ I.ideal V) := by
  let _ := (f.appLE U V e).hom.toAlgebra
  rw [← RingHom.quasiFinite_algebraMap, ← open_subscheme_quotient_structureMap f I U V e]
  apply RingHom.QuasiFinite.comp
    (.of_finite (RingHom.Finite.of_surjective _
      (I.subschemeObjIso V).commRingCatIsoToRingEquiv.surjective))
    (HasRingHomProperty.appLE @LocallyQuasiFinite (I.subschemeι ≫ f) inferInstance
      U ⟨_, V.2.preimage I.subschemeι⟩ _)

/-- Finite presentation of the family supplies algebra presentation on every affine chart. -/
theorem finitePresentation_open_subscheme_ideal_quotient
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)] :
    let _ := (f.appLE U V e).hom.toAlgebra
    Algebra.FinitePresentation Γ(Y, U) (Γ(X, V) ⧸ I.ideal V) := by
  let _ := (f.appLE U V e).hom.toAlgebra
  rw [← RingHom.finitePresentation_algebraMap,
    ← open_subscheme_quotient_structureMap f I U V e]
  apply RingHom.FinitePresentation.comp
    (.of_surjective _ (I.subschemeObjIso V).commRingCatIsoToRingEquiv.surjective ?_)
    ((I.subschemeι ≫ f).finitePresentation_appLE U.2 (V.2.preimage I.subschemeι) _)
  change (RingHom.ker (I.subschemeObjIso V).commRingCatIsoToRingEquiv.toRingHom).FG
  rw [RingEquiv.toRingHom_eq_coe, RingHom.ker_coe_equiv]
  exact Submodule.fg_bot

end FLT.Mazur.FCurve
