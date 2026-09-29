/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoherent
public import FLT.Mazur.CoherentDevissage
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.RingTheory.Support

/-!
# Support of affine module sheaves

The canonical map into the actual additive stalk of `tilde M` is a module
localization. Its scalar action comes from the structure sheaf stalk. Consequently
the nonzero-stalk support agrees with algebraic module support, and for finite
modules it is the zero locus of the annihilator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {R : CommRingCat.{u}}

/-- The scheme stalk acts on the tilde stalk via the module sheaf action. -/
instance tildeStalkModule (M : ModuleCat.{u} R) (x : PrimeSpectrum R) :
    Module ((structurePresheafInCommRingCat R).stalk x) ((tilde M).presheaf.stalk x) :=
  inferInstanceAs (Module ((structurePresheafInCommRingCat R).stalk x)
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x))

/-- Identify the actual additive stalk with localization of the coefficient module. -/
def tildeStalkEquiv (M : ModuleCat.{u} R) (x : PrimeSpectrum R) :
    (tilde M).presheaf.stalk x ≃ₗ[R] LocalizedModule x.asIdeal.primeCompl M :=
  (IsLocalizedModule.iso x.asIdeal.primeCompl (tilde.toStalk M x).hom).symm

/-- Coefficients map to fractions with denominator one. -/
@[simp]
lemma tildeStalkEquiv_toStalk (M : ModuleCat.{u} R) (x : PrimeSpectrum R) (m : M) :
    tildeStalkEquiv M x (tilde.toStalk M x m) = LocalizedModule.mk m 1 :=
  IsLocalizedModule.iso_symm_apply _ _ _

/-- The comparison respects the action of coefficient germs in the scheme stalk. -/
lemma tildeStalkEquiv_smul_germ (M : ModuleCat.{u} R) (x : PrimeSpectrum R)
    (r : R) (m : (tilde M).presheaf.stalk x) :
    tildeStalkEquiv M x (StructureSheaf.toStalk R x r • m) =
      r • tildeStalkEquiv M x m :=
  (tildeStalkEquiv M x).map_smul r m

/-- A tilde stalk vanishes exactly when the localized coefficient module vanishes. -/
lemma tilde_stalk_isZero_iff (M : ModuleCat.{u} R) (x : PrimeSpectrum R) :
    IsZero ((stalk x).obj (tilde M)) ↔
      Subsingleton (LocalizedModule x.asIdeal.primeCompl M) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact (tildeStalkEquiv M x).toEquiv.subsingleton_congr

/-- Nonzero stalks are precisely nonzero localizations. -/
lemma mem_support_tilde_iff (M : ModuleCat.{u} R) (x : PrimeSpectrum R) :
    x ∈ support (tilde M) ↔ Nontrivial (LocalizedModule x.asIdeal.primeCompl M) := by
  change (¬ IsZero ((stalk x).obj (tilde M))) ↔ _
  rw [tilde_stalk_isZero_iff, not_subsingleton_iff_nontrivial]

/-- Geometric support agrees with the support of the original module. -/
theorem support_tilde (M : ModuleCat.{u} R) :
    support (tilde M) = Module.support R M :=
  Set.ext (mem_support_tilde_iff M)

/-- For a finite module, the stalk at a prime is nonzero iff the prime contains its
annihilator. -/
lemma mem_support_tilde_iff_annihilator (M : ModuleCat.{u} R) [Module.Finite R M]
    (x : PrimeSpectrum R) :
    x ∈ support (tilde M) ↔ Module.annihilator R M ≤ x.asIdeal := by
  rw [support_tilde]
  exact Module.mem_support_iff_of_finite

/-- The support of a finite tilde module is the closed set defined by its annihilator. -/
theorem support_tilde_eq_zeroLocus (M : ModuleCat.{u} R) [Module.Finite R M] :
    support (tilde M) = PrimeSpectrum.zeroLocus (Module.annihilator R M) := by
  rw [support_tilde, Module.support_eq_zeroLocus]

/-- Finite tilde modules have closed support over any commutative ring. -/
theorem isClosed_support_tilde (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsClosed (support (tilde M)) := by
  rw [support_tilde_eq_zeroLocus]
  exact PrimeSpectrum.isClosed_zeroLocus _

/-- A locally finitely presented affine sheaf has support defined by the annihilator
of its actual global sections. -/
theorem support_affine_eq_zeroLocus (M : (Spec R).Modules) [M.IsFinitePresentation] :
    support M = PrimeSpectrum.zeroLocus (Module.annihilator R Γ(M, ⊤)) := by
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := affineCoherent_finite_sections M
  rw [support_iso (affineCoherentIso M), support_tilde_eq_zeroLocus]
  rfl

/-- Local finite presentation suffices for closed support on an affine scheme. -/
theorem isClosed_support_affine (M : (Spec R).Modules) [M.IsFinitePresentation] :
    IsClosed (support M) := by
  rw [support_affine_eq_zeroLocus]
  exact PrimeSpectrum.isClosed_zeroLocus _

end FLT.Mazur.FCurve.CoherentDevissage
