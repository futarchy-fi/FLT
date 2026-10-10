/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechAffineGeneric
public import FLT.Mazur.PrincipalOpenSectionAlgebra

/-!
# Actual section comparison on one original-base principal open

The localization action is constructed from geometric factorization. The generic
open is indexed by a nonzero element of the original ring, using its canonical
identification with the structural ring of its spectrum.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.IncreasingCechCartesian
open IncreasingCechScalars FCurve Chow PrincipalOpenSectionAlgebra

variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) [IsAffine T] [IsAffine S] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
  (r : Γ(S, ⊤)) (hr : IsUnit (g.appTop r))

/-- The actual comparison, with its localization action constructed from invertibility. -/
def principalSectionsComparison :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    let _ := sectionAlgebra g r hr
    Γ(T, ⊤) ⊗[Localization.Away r]
      LocalizedModule (Submonoid.powers r)
        (baseSections (structureModule X) f.appTop.hom ⊤) →+
          baseSections (structureModule P) q.appTop.hom ⊤ := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let _ := sectionAlgebra g r hr
  let _ := sectionAlgebra_tower g r hr
  exact localizedSectionsComparison h U hU hCover (Submonoid.powers r)

variable (f)

include hU hCover in
/-- One generic principal open works for all actual affine factorizations through it. -/
theorem exists_principal_sectionsComparison_bijective
    [IsNoetherianRing Γ(S, ⊤)] [IsDomain Γ(S, ⊤)] [IsProper f] [Flat f] :
    ∃ r : Γ(S, ⊤), r ≠ 0 ∧ ∀ {P T : Scheme.{0}}
      {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
      (h : IsPullback p q f g) [IsAffine T]
      (t : T ⟶ (S.basicOpen r).toScheme) (ht : t ≫ (S.basicOpen r).ι = g),
      Function.Bijective (principalSectionsComparison h U hU hCover r
        (isUnit_of_factor g r t ht)) := by
  obtain ⟨r, hr, hk⟩ := exists_affine_generic_tensorKer_bijective f U hU hCover
  refine ⟨r, hr, ?_⟩
  intro P T p q g h _ t ht
  let hu := isUnit_of_factor g r t ht
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let _ := sectionAlgebra g r hu
  let _ := sectionAlgebra_tower g r hu
  dsimp only [principalSectionsComparison]
  apply localizedSectionsComparison_bijective
  exact hk 0 Γ(T, ⊤)

variable {R : CommRingCat.{0}} [IsNoetherianRing R] [IsDomain R]
  (fR : X ⟶ Spec R) [IsProper fR] [Flat fR]

include hU hCover in
/-- The generic open is defined by a nonzero element of the original coefficient ring. -/
theorem exists_original_principal_sectionsComparison_bijective :
    ∃ r : R, r ≠ 0 ∧ ∀ {P T : Scheme.{0}}
      {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ Spec R}
      (h : IsPullback p q fR g) [IsAffine T]
      (t : T ⟶ ((Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r)).toScheme)
      (ht : t ≫ ((Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r)).ι = g),
      Function.Bijective (principalSectionsComparison h U hU hCover
        ((Scheme.ΓSpecIso R).inv r)
        (isUnit_of_factor g ((Scheme.ΓSpecIso R).inv r) t ht)) := by
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  let _ : IsNoetherianRing Γ(Spec R, ⊤) := isNoetherianRing_of_ringEquiv R e.symm
  let _ : IsDomain Γ(Spec R, ⊤) := e.toMulEquiv.isDomain R
  obtain ⟨s, hs, hk⟩ := exists_principal_sectionsComparison_bijective fR U hU hCover
  refine ⟨e s, fun hz ↦ hs (e.injective (hz.trans (map_zero e).symm)), ?_⟩
  have he : (Scheme.ΓSpecIso R).inv (e s) = s := e.symm_apply_apply s
  rw [he]
  exact @hk

end FLT.Mazur.IncreasingCechCartesian
