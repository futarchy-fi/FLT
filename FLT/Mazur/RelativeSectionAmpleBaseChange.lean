/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleCartesianAffineOpen
public import FLT.Mazur.AmplePrincipalLocality

/-!
# Relative section ampleness under arbitrary base change

Principal neighborhoods in an affine new base map into affine opens of the
original base. Their sections extend with exact generator loci, proving
ampleness on the entire affine inverse image. No Noetherian hypothesis is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
variable {X Y S T : Scheme.{0}} {f : X ⟶ S} {g : T ⟶ S}
  {p : Y ⟶ X} {q : Y ⟶ T} {L : X.Modules}

/-- Over an affine new base, the pulled-back line bundle is absolutely ample. -/
theorem RelativelyAmpleLineBundle.ample_of_isPullback_affineTarget
    (hL : RelativelyAmpleLineBundle f L) (sq : IsPullback p q f g)
    [IsAffine T] [IsSeparated q] : AmpleLineBundle ((Scheme.Modules.pullback p).obj L) := by
  have : QuasiCompact q := MorphismProperty.of_isPullback sq hL.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from q]; infer_instance⟩
  apply ampleLineBundle_of_principal_neighborhoods (hL.2.1.pullback p)
  intro y
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show g (q y) ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨r, hrV, hyr⟩ := (isAffineOpen_top T).exists_basicOpen_le
    (⟨q y, hyV⟩ : g ⁻¹ᵁ V) (show q y ∈ (⊤ : T.Opens) from trivial)
  refine ⟨q.appTop r, ?_, ?_⟩
  · rw [← Scheme.Hom.preimage_basicOpen_top]
    exact hyr
  · have h := hL.ample_cartesian_affineOpen sq V hV (T.basicOpen r)
      ((isAffineOpen_top T).basicOpen r) hrV
    rwa [Scheme.Hom.preimage_basicOpen_top] at h

/-- Separated relative section ampleness survives every cartesian square. -/
theorem RelativelyAmpleLineBundle.of_isPullback [IsSeparated f]
    (hL : RelativelyAmpleLineBundle f L) (sq : IsPullback p q f g) :
    RelativelyAmpleLineBundle q ((Scheme.Modules.pullback p).obj L) := by
  have : QuasiCompact q := MorphismProperty.of_isPullback sq hL.1
  have : IsSeparated q := MorphismProperty.of_isPullback sq inferInstance
  refine ⟨inferInstance, hL.2.1.pullback p, fun U hU ↦ ?_⟩
  let : IsAffine U.toScheme := hU
  have hs := (isPullback_morphismRestrict q U).flip.paste_horiz sq
  exact (hL.ample_of_isPullback_affineTarget hs).of_iso
    ((restrictFunctorIsoPullback (q ⁻¹ᵁ U).ι).app _ ≪≫
      (pullbackComp (q ⁻¹ᵁ U).ι p).app L)

/-- Arbitrary base change preserves relative section ampleness of a separated morphism. -/
theorem RelativelyAmpleLineBundle.baseChange [IsSeparated f]
    (hL : RelativelyAmpleLineBundle f L) (g : T ⟶ S) :
    RelativelyAmpleLineBundle (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L) :=
  hL.of_isPullback (IsPullback.of_hasPullback f g)

end FLT.Mazur.FCurve
