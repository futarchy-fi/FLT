/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalSection
public import FLT.Mazur.ModuleSectionUnit

/-!
# The canonical divisor section generates off its support

The actual section morphism is an isomorphism on any open disjoint from the
support. The proof checks affine subopens through the dual-ideal coordinates.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- An ideal is the unit ideal on an affine open disjoint from its support. -/
lemma ideal_eq_top_of_disjoint_support (I : X.IdealSheafData) (V : X.affineOpens)
    (hV : ∀ x ∈ V.1, x ∉ I.support) : I.ideal V = ⊤ := by
  have hz : X.zeroLocus (U := V.1) (I.ideal V) ∩ V.1 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hV x hx.2 ((I.mem_support_iff_of_mem hx.2).mpr hx.1)
  have he := V.2.fromSpec_image_zeroLocus (I.ideal V)
  rw [hz] at he
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.image_eq_empty.mp he)

/-- The canonical section is an isomorphism on every open off the divisor. -/
theorem divisorSection_isIso_off_support (hI : EffectiveCartier I) (U : X.Opens)
    (hU : ∀ x ∈ U, x ∉ I.support) :
    IsIso (sectionHom (divisorLineBundle I hI) U (divisorSection hI U)) := by
  let W (V : U.toScheme.affineOpens) : X.affineOpens :=
    ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.ι⟩
  have hW (V : U.toScheme.affineOpens) : I.ideal (W V) = ⊤ :=
    ideal_eq_top_of_disjoint_support I (W V) (fun x hx ↦ hU x (U.ι_image_le V.1 hx))
  have hC (V : U.toScheme.affineOpens) : CartierChart I (W V) :=
    ⟨1, isRegular_one, by simp [hW V]⟩
  apply sectionHom_isIso_of_affine_coordinates _ U _
    (fun V ↦ ((hC V).divisorSectionsEquiv hI).trans (hC V).dualEquiv)
  intro V
  change IsUnit ((hC V).dualEquiv (divisorChartEval I (W V)
    ((divisorLineBundle I hI).presheaf.map _ (divisorSection hI U))))
  rw [divisorSection_restrict, divisorSection_coordinate]
  rw [← Ideal.span_singleton_eq_top, ← (hC V).choose_spec.2, hW V]

/-- In particular, the canonical section trivializes the complement of the support. -/
theorem divisorSection_isIso_complement (hI : EffectiveCartier I) :
    IsIso (sectionHom (divisorLineBundle I hI) I.support.compl
      (divisorSection hI I.support.compl)) :=
  divisorSection_isIso_off_support hI _ (fun _ hx ↦ hx)

end FLT.Mazur.FCurve
