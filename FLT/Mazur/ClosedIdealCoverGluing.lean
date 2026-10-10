/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedIdealCoverRestriction
public import FLT.Mazur.MonoFamilySchemeGluing

/-!
# Effective gluing of compatible closed families on an open cover

Compatible actual ideal sheaves produce an actual glued scheme over the
ambient base. Its chart squares are cartesian, identifying the original
closed families with the inverse images of the base cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (C : X.OpenCover.{u})
variable (J : ∀ i : C.I₀, (C.X i).IdealSheafData)
variable (hJ : ∀ i j, (J i).comap (pullback.fst (C.f i) (C.f j)) =
  (J j).comap (pullback.snd (C.f i) (C.f j)))

/-- Each local closed family is a monomorphism into the original ambient scheme. -/
local instance chartToBase_mono (i : C.I₀) : Mono (chartToBase C J i) :=
  inferInstanceAs (Mono ((J i).subschemeι ≫ C.f i))

/-- The actual gluing data of the compatible local closed families. -/
def glueData : Scheme.GlueData := by
  let _ : ∀ i j, IsOpenImmersion (pullback.fst (chartToBase C J i) (chartToBase C J j)) :=
    intersection_fst_isOpenImmersion C J hJ
  exact MonoFamilyGluing.glueData (chartToBase C J)

/-- The actual glued family maps to the ambient base. -/
def toBase : (glueData C J hJ).glued ⟶ X := by
  let _ : ∀ i j, IsOpenImmersion (pullback.fst (chartToBase C J i) (chartToBase C J j)) :=
    intersection_fst_isOpenImmersion C J hJ
  exact MonoFamilyGluing.toAmbient (chartToBase C J)

/-- The glued map restricts to the original local closed family map. -/
@[reassoc]
theorem ι_toBase (i : C.I₀) :
    (glueData C J hJ).ι i ≫ toBase C J hJ = chartToBase C J i := by
  let _ : ∀ i j, IsOpenImmersion (pullback.fst (chartToBase C J i) (chartToBase C J j)) :=
    intersection_fst_isOpenImmersion C J hJ
  exact MonoFamilyGluing.ι_toAmbient (chartToBase C J) i

/-- The inverse image of a base chart is precisely the corresponding glued family chart. -/
theorem preimage_toBase (i : C.I₀) :
    (toBase C J hJ) ⁻¹ᵁ (C.f i).opensRange = ((glueData C J hJ).ι i).opensRange := by
  apply TopologicalSpace.Opens.coe_inj.mp
  ext x
  change (∃ ui, C.f i ui = toBase C J hJ x) ↔ ∃ zi, (glueData C J hJ).ι i zi = x
  constructor
  · rintro ⟨ui, hui⟩
    obtain ⟨j, zj, rfl⟩ := (glueData C J hJ).ι_jointly_surjective x
    have hz : chartToBase C J j zj = C.f i ui := by
      rw [← ι_toBase C J hJ j]
      exact hui.symm
    obtain ⟨y, hy, _⟩ := Scheme.Pullback.exists_preimage_pullback zj ui hz
    let q := restriction_isPullback C J hJ j i
    let z := q.isoPullback.hom y
    have hfirst : pullback.fst (chartToBase C J j) (chartToBase C J i) z = zj :=
      (congrArg (fun f ↦ f y) q.isoPullback_hom_fst).trans hy
    refine ⟨pullback.snd (chartToBase C J j) (chartToBase C J i) z, ?_⟩
    have hc := (glueData C J hJ).glue_condition j i
    change (pullbackSymmetry _ _).hom ≫ pullback.fst _ _ ≫ _ = pullback.fst _ _ ≫ _ at hc
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst] at hc
    have he := congrArg (fun f ↦ f z) hc
    simpa only [Scheme.Hom.comp_apply, hfirst] using! he
  · rintro ⟨zi, rfl⟩
    refine ⟨(J i).subschemeι zi, ?_⟩
    have he := congrArg (fun f ↦ f zi) (ι_toBase C J hJ i)
    exact he.symm

/-- The original local closed family is the actual base change of the glued family. -/
theorem chart_isPullback (i : C.I₀) :
    IsPullback (J i).subschemeι ((glueData C J hJ).ι i) (C.f i) (toBase C J hJ) :=
  IsOpenImmersion.isPullback _ _ _ _ (ι_toBase C J hJ i) (preimage_toBase C J hJ i)

/-- A compatible closed family on an open cover glues to an actual closed immersion. -/
instance toBase_isClosedImmersion : IsClosedImmersion (toBase C J hJ) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) C
  intro i
  change IsClosedImmersion (pullback.snd (toBase C J hJ) (C.f i))
  rw [← (chart_isPullback C J hJ i).flip.isoPullback_inv_snd]
  infer_instance

/-- The kernel ideal of the glued closed immersion recovers each original chart ideal. -/
theorem ker_toBase_comap (i : C.I₀) : (toBase C J hJ).ker.comap (C.f i) = J i := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso (chart_isPullback C J hJ i).isoPullback.hom,
    IsPullback.isoPullback_hom_fst, Scheme.IdealSheafData.ker_subschemeι]

end FLT.Mazur.ClosedIdealCover
