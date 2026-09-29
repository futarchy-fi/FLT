/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleSupport
public import FLT.Mazur.CoherentSubquotient

/-!
# Closed support of locally finitely presented module sheaves

Support commutes with restriction along open immersions. On each affine open,
a locally finitely presented sheaf has support defined by the annihilator of its
finite module of sections, so its support is closed globally. Empty support is
equivalent to being a zero object, even without a finiteness hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X Y : Scheme.{u}}

/-- Restriction along an open immersion preserves the stalk at the corresponding point. -/
lemma mem_support_restrict (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    y ∈ support (M.restrict f) ↔ f y ∈ support M :=
  not_congr ((Scheme.Modules.restrictStalkNatIso f y).app M).isZero_iff

/-- Support commutes with restriction along any open immersion. -/
theorem support_restrict (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f] :
    support (M.restrict f) = f ⁻¹' support M :=
  Set.ext (mem_support_restrict M f)

/-- In the ambient scheme, restriction intersects support with the open image. -/
lemma image_support_restrict (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f] :
    f '' support (M.restrict f) = support M ∩ Set.range f := by
  rw [support_restrict, Set.image_preimage_eq_inter_range]

/-- Restriction to an open subset has exactly the intersection with that subset as support. -/
lemma image_support_restrict_open (M : X.Modules) (U : X.Opens) :
    U.ι '' support (M.restrict U.ι) = support M ∩ U := by
  rw [image_support_restrict]
  simp

/-- On an affine chart, support is defined by the annihilator of actual sections. -/
theorem preimage_support_affine (M : X.Modules) [M.IsFinitePresentation]
    {R : CommRingCat.{u}} (f : Spec R ⟶ X) [IsOpenImmersion f] :
    f ⁻¹' support M =
      PrimeSpectrum.zeroLocus (Module.annihilator R Γ(M.restrict f, ⊤)) := by
  have := coherentPresentation_restrict f M
  rw [← support_restrict, support_affine_eq_zeroLocus]

/-- Support of a locally finitely presented sheaf is closed, with no Noetherian
hypothesis on the scheme. -/
theorem isClosed_support (M : X.Modules) [M.IsFinitePresentation] :
    IsClosed (support M) := by
  rw [IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top X)]
  intro U
  rw [← U.2.isoSpec.inv.homeomorph.isClosed_preimage]
  change IsClosed (U.2.fromSpec ⁻¹' support M)
  rw [preimage_support_affine]
  exact PrimeSpectrum.isClosed_zeroLocus _

/-- The closed support attached to the existing nonzero-stalk support. -/
def closedSupport (M : X.Modules) [M.IsFinitePresentation] : Closeds X :=
  ⟨support M, isClosed_support M⟩

@[simp]
lemma coe_closedSupport (M : X.Modules) [M.IsFinitePresentation] :
    (closedSupport M : Set X) = support M := rfl

/-- Vanishing of every additive stalk detects the zero module sheaf. -/
theorem isZero_iff_stalk_isZero (M : X.Modules) :
    IsZero M ↔ ∀ x : X, IsZero ((stalk x).obj M) := by
  refine ⟨fun h x ↦ (stalk x).map_isZero h, fun h ↦ ?_⟩
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hz : IsZero (F.obj M) :=
    (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (F.obj M)).mpr h
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  apply F.map_injective
  simpa using hz

/-- Empty support is equivalent to the actual module sheaf being zero. -/
theorem support_eq_empty_iff_isZero (M : X.Modules) :
    support M = ∅ ↔ IsZero M := by
  rw [isZero_iff_stalk_isZero]
  simp only [Set.eq_empty_iff_forall_notMem, support, Set.mem_ofPred_eq, not_not]

end FLT.Mazur.FCurve.CoherentDevissage
