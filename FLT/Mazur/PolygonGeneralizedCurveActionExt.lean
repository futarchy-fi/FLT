/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonGeneralizedCurve
public import FLT.Mazur.PolygonParameterizedHomExt
public import FLT.Mazur.GeneralizedCurveBaseChangeIso

/-!
# Polygon whole actions are determined on the smooth group

The original component tori detect maps from the full action domain into a
separated target. Thus a group comparison preserving the smooth inclusion
is automatically equivariant on the entire polygon, including its nodes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonGeneralizedCurve
open PolygonPinching PolygonUniversalAction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
local notation "E" => curve K n hn p q h

/-- The smooth second input detects maps on the original whole polygon action domain. -/
theorem actionDomain_hom_ext {Y : Over (Spec (.of K))} [IsSeparated Y.hom]
    (f g : (E).group ⊗ C ⟶ Y)
    (he : (E).group ◁ (E).inclusion ≫ f = (E).group ◁ (E).inclusion ≫ g) : f = g := by
  apply parameterized_hom_ext K n hn p q h (G K n)
  intro i
  let e := coproductUniqueIso (fun _ : PUnit => component K)
  apply (cancel_epi ((G K n) ◁ e.hom)).mp
  apply PolygonSplitGroup.tensor_hom_ext (fun _ : ZMod n => gm K)
    (fun _ : PUnit => component K)
  intro a j
  simp only [tensorHom_comp_whiskerLeft_assoc, e, ι_coproductUniqueIso_hom,
    eqToHom_refl, Category.id_comp]
  apply ProjectiveLineProductCharts.product_hom_ext_torus K (LaurentPolynomial K)
  have hi : PolygonSplitGroup.component K n (ZMod.finEquiv n i) ≫ (E).inclusion =
      torusToComponent K ≫ componentι K n i ≫ p := by
    let _ := polygon_lfp K n hn p q h
    change PolygonSplitGroup.component K n (ZMod.finEquiv n i) ≫
      PolygonActionSmooth.smoothMap K n hn p q h = _
    simpa only [RingEquiv.symm_apply_apply] using
      PolygonActionSmooth.component_smoothMap K n hn p q h (ZMod.finEquiv n i)
  have hh := congrArg
    ((PolygonSplitGroup.component K n a ⊗ₘ
      PolygonSplitGroup.component K n (ZMod.finEquiv n i)) ≫ ·) he
  change (_ ⊗ₘ _) ≫ (G K n) ◁ (E).inclusion ≫ f =
    (_ ⊗ₘ _) ≫ (G K n) ◁ (E).inclusion ≫ g at hh
  simpa only [tensorHom_comp_whiskerLeft_assoc, hi,
    whiskerLeft_comp_tensorHom_assoc, Category.assoc] using hh

/-- A smooth group homomorphism preserving the inclusion preserves the whole action. -/
theorem action_of_inclusion {F : GeneralizedEllipticCurve (Spec (.of K))}
    (c : (E).curve ⟶ F.curve) (g : (E).group ⟶ F.group) [IsMonHom g]
    (hi : (E).inclusion ≫ c = g ≫ F.inclusion) :
    (E).act ≫ c = (g ⊗ₘ c) ≫ F.act := by
  let _ := F.family.family.1
  apply actionDomain_hom_ext K n hn p q h
  rw [← Category.assoc, (E).action_inclusion, Category.assoc, hi]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, hi]
  rw [← tensorHom_comp_whiskerLeft_assoc, F.action_inclusion, ← IsMonHom.mul_hom_assoc]

/-- Compatible whole-curve and smooth-group isomorphisms identify the full DR polygon. -/
def isoOfInclusion {F : GeneralizedEllipticCurve (Spec (.of K))}
    (c : (E).curve ≅ F.curve) (g : (E).group ≅ F.group) [IsMonHom g.hom]
    (hi : (E).inclusion ≫ c.hom = g.hom ≫ F.inclusion) : (E) ≅ F :=
  GeneralizedEllipticCurve.isoMk c g hi (action_of_inclusion K n hn p q h c.hom g.hom hi)

end FLT.Mazur.PolygonGeneralizedCurve
