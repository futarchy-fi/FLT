/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenPairPrincipalRestriction

/-!
# Restricting open section equations along genuine scheme maps

Pair equations on a nonstable open can be pulled back wherever both
endpoints land in that open. Boundary equations and full pair equations
are preserved under arbitrary open refinement, including nonaffine cores.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Z T : Scheme} (O : X.Opens) (f g : Z ⟶ X)

/-- An open-pair equation pulls back along any actual pair of factorizations. -/
theorem pairOpen_equation_pullback (v : Γ(O.toScheme, ⊤))
    (hv : (pairOpenFirst O f g).appTop v = (pairOpenSecond O f g).appTop v)
    (q : T ⟶ Z) (a b : T ⟶ O.toScheme)
    (ha : a ≫ O.ι = q ≫ f) (hb : b ≫ O.ι = q ≫ g) :
    a.appTop v = b.appTop v := by
  let D := pairOpenDomain O f g
  have hr : Set.range q ⊆ Set.range D.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (q x) ∈ O ∧ g (q x) ∈ O
    constructor
    · have h := congrArg (fun k : T ⟶ X ↦ k x) ha
      exact h ▸ (a x).property
    · have h := congrArg (fun k : T ⟶ X ↦ k x) hb
      exact h ▸ (b x).property
  let l := IsOpenImmersion.lift D.ι q hr
  have hl : l ≫ D.ι = q := IsOpenImmersion.lift_fac _ _ _
  have hla : l ≫ pairOpenFirst O f g = a := by
    apply (cancel_mono O.ι).mp
    rw [Category.assoc, pairOpenFirst, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, hl, ha]
  have hlb : l ≫ pairOpenSecond O f g = b := by
    apply (cancel_mono O.ι).mp
    rw [Category.assoc, pairOpenSecond, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, hl, hb]
  rw [← hla, ← hlb, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  exact congrArg (fun t ↦ l.appTop t) hv

/-- Both relation endpoints may be restricted to any smaller open. -/
theorem pairOpen_equation_refine (V : X.Opens) (hVO : V ≤ O)
    (v : Γ(O.toScheme, ⊤))
    (hv : (pairOpenFirst O f g).appTop v = (pairOpenSecond O f g).appTop v) :
    (pairOpenFirst V f g).appTop ((X.homOfLE hVO).appTop v) =
      (pairOpenSecond V f g).appTop ((X.homOfLE hVO).appTop v) := by
  apply pairOpen_equation_pullback O f g v hv (pairOpenDomain V f g).ι
    (pairOpenFirst V f g ≫ X.homOfLE hVO)
    (pairOpenSecond V f g ≫ X.homOfLE hVO)
  · simp only [Category.assoc, Scheme.homOfLE_ι, pairOpenFirst,
      Scheme.Hom.resLE_comp_ι]
  · simp only [Category.assoc, Scheme.homOfLE_ι, pairOpenSecond,
      Scheme.Hom.resLE_comp_ι]

/-- Exact boundary values survive restriction to a smaller open. -/
theorem open_boundary_equation_refine (V : X.Opens) (hVO : V ≤ O)
    (i : Z ⟶ X) (v : Γ(O.toScheme, ⊤)) (t : Γ(Z, ⊤))
    (hb : (i ∣_ O).appTop v = (i ⁻¹ᵁ O).ι.appTop t) :
    (i ∣_ V).appTop ((X.homOfLE hVO).appTop v) = (i ⁻¹ᵁ V).ι.appTop t := by
  have hpre : i ⁻¹ᵁ V ≤ i ⁻¹ᵁ O := fun _ hx ↦ hVO hx
  have hs : (i ∣_ V) ≫ X.homOfLE hVO = Z.homOfLE hpre ≫ (i ∣_ O) := by
    apply (cancel_mono O.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι,
      Scheme.homOfLE_ι_assoc]
  change ((i ∣_ V) ≫ X.homOfLE hVO).appTop v = _
  rw [hs, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hb]
  change (Z.homOfLE hpre ≫ (i ⁻¹ᵁ O).ι).appTop t = _
  rw [Scheme.homOfLE_ι]

end FLT.Mazur.SchemeFiniteGroupQuotient
