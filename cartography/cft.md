# FLT-on-Lean: class field theory and solvable extensions

Scope: this map was made from read-only greps/reads of `/Users/kas/FLT` and its
checked-out Mathlib dependency.  No literature lookup or network access was
used.  Statements about Neukirch/Milne routes or historical theorem strength
are marked **(literature-verify)**.

## Grep ledger and sibling-map verification

The project-source grep (`blueprint/`, `FLT/Assumptions/`, and project Lean
sources) produced these relevant hits:

* The CFT appendix is explicit: `chtopbestiary.tex:5` is “Results from class
  field theory”; `:24-29` states local reciprocity and mentions a Lubin--Tate
  formalisation; `:83-86` states global reciprocity; `:90-94` states the
  solvable-extension consequence; and `:96` says Poitou--Tate is still needed.
* `ch04overview.tex:29` lists “several nontrivial results in global class
  field theory” in potential modularity.  `:46-47` says local class field
  theory (or an elementary substitute) gives the inertia map
  (I_v\to\mathcal O_{F_v}^{\times}\to k(v)^{\times}).  The modularity
  lifting theorem has an explicit `\uses{Skinner_Wiles_CFT_trick,...}` edge at
  `:66-72`; its proof sketch says the Skinner--Wiles trick needs cyclic base
  change at `:86-88`.
* `FLT/Assumptions/README.md:36-37` records the formalizable assumption
  “Existence of a solvable extension ... with prescribed behaviour ... (the
  proof uses class field theory).”  The same README lists Poitou--Tate at
  `:65-68`.
* `FLT/GaloisRepresentation/Automorphic.lean:109-125` documents cyclic base
  change with a finite solvable (E/F), and `:127-133` makes solvability an
  input typeclass `[Group.IsSolvable (E ≃ₐ[F] E)]`, not a CFT construction.
* `FLT/GlobalLanglandsConjectures/GLzero.lean:13-27` is historical
  commentary; it says Wiles used “class field theory (in the form of global
  Tate duality)” but contains no CFT declaration or proof.
* `FLT/DedekindDomain/FiniteAdeleRing/LocalUnits.lean:28`, `:90-92`, and
  `:113-117` define finite-idele/local-unit constructors.  These are adelic
  substrate, not applications of reciprocity.
* Other hits are not CFT consumers: `ch07exampleGLn.tex:6,10` uses
  “reciprocity” for Langlands conjectures; `ch03freyreduction.tex:265` is the
  Brauer--Nesbitt theorem; `ch04overview.tex:104` is the Brauer theorem trick;
  `FLT/Mathlib/LinearAlgebra/Determinant.lean:62-65` and
  `FLT/Mathlib/RingTheory/SimpleRing/TensorProduct.lean:23-26` are Brauer-group
  comments/API prerequisites.  The project grep returned no `Kummer` hit.

The supplied sibling claims therefore drift in the current checkout.  There
is no separate Poitou--Tate chapter: only the unformalized sentence at
`chtopbestiary.tex:96` and the README entry above.  No project hit mentions
Brauer invariants or Kummer theory, and the only idele hits are the concrete
constructors just cited.  No “Mazur D6” file/map is present in the searched
workspace; `Mazur.lean:41-49` discusses schemes/cohomology and has no CFT edge.
The cyclic-base-change claim is only partly true: solvability is indeed an
input at `Automorphic.lean:131-133`, while the CFT-produced extension is the
separate Skinner--Wiles/Assumptions item.

## Consumer inventory

Size labels: **S** = a few definitions/lemmas or an axiom interface; **M** = a
small coherent API; **L** = a major theorem/module; **XL** = a full research-
scale development.  “Weakest slice” means the smallest CFT interface that
would serve the cited consumer, not the strength of a traditional proof.

### 1. Local reciprocity / local CFT foundation

**Citations.** `blueprint/src/chapter/chtopbestiary.tex:11-20` defines the
maximal-unramified extension and Weil group; `:24-29` states the local CFT
isomorphism (K^{\times}\simeq W_K^{\mathrm{ab}}) and points to a
 Lubin--Tate formalisation.

> “If $K$ is a finite extension of $\\Q_p$ then there are two ``canonical''
> isomorphisms ... between $K^\\times$ and the abelianisation of the Weil
> group of $K$.” (`chtopbestiary.tex:24-25`)

**Needs.** A topological local field, inertia/unramified quotient, and a
continuous local Artin map with the arithmetic/geometric Frobenius convention.
The full topological isomorphism is what the appendix states; downstream item
2 only needs a much smaller character/map interface.

**Weakest sufficient slice.** For item 2, a local reciprocity character on
inertia and reduction to residue-field units suffices; for a reusable CFT
module, retain finite-abelian-extension reciprocity and functoriality.  No
global existence theorem is needed here; local CFT alone suffices.

**Size / edges / risks.** **M** for the narrow map API, **XL** for proving the
full theorem.  `local_Weil_group → local_class_field_theory → global_class_field_theory`
is an explicit blueprint edge (`:19`, `:24`, `:83`).  Risks are topological
profinite definitions, Frobenius sign conventions, and connecting local
fields to the repository's `adicCompletion` types.

**Reference route.** Local reciprocity via Lubin--Tate, with the norm and
unit-filtration API, is the first stage of the standard Neukirch/Milne route
**(literature-verify)**.

### 2. Inertia character used in the modularity-lifting statement

**Citations.** `blueprint/src/chapter/ch04overview.tex:44-47` defines (I_v),
then says “Local class field theory (or a more elementary approach)” gives
(I_v\to\mathcal O_{F_v}^{\times}\to k(v)^{\times}), whose kernel is (J_v).

> “Local class field theory (or a more elementary approach) gives a map
> $I_v\\to\\calO_{F_v}^\\times$ and hence a map $I_v\\to k(v)^\\times$.”
> (`ch04overview.tex:46-47`)

**Needs.** Only the displayed map, its continuity/compatibility, and the
kernel (J_v).  It does **not** need the global Artin map, ray-class fields,
or an existence theorem.  An elementary tame-inertia construction would avoid
even full local CFT.

**Weakest slice.** **Narrow local reciprocity/tame inertia** (or an elementary
substitute); local CFT alone is sufficient and global CFT is unnecessary.

**Size / edges / risks.** **S–M**.  Edge: this map is used in the definition of
“(S)-good” representations (`:49-60`) and hence in the modularity-lifting
theorem (`:66-77`).  Risk: the blueprint leaves the map informal, while the
Lean theorem currently uses `localTameAbelianInertiaGroup` in its hypotheses
(`FLT/GaloisRepresentation/Automorphic.lean:169-178`) without a CFT proof.

### 3. Global reciprocity theorem (idele class group)

**Citations.** `blueprint/src/chapter/chtopbestiary.tex:79-86` states two
canonical maps between 
(\pi_0(\mathbb A_N^{\times}/N^{\times})) and (G_N^{\mathrm{ab}}),
compatible with the local maps, and calls this the main global CFT theorem.
The theorem has `\uses{local_class_field_theory}` at `:83`.

> “there are two ``canonical'' isomorphisms of topological groups between the
> profinite abelian groups $\\pi_0(\\A_N^\\times/N^\\times)$ and $\\GN^{\\ab}$”
> (`chtopbestiary.tex:83-84`).

**Needs.** Topological finite/infinite adeles, the idele class quotient, local
uniformisers, the global Artin map, local-global compatibility, and the
arithmetic/geometric Frobenius choice.  The statement is reciprocity itself;
it does not by itself assert a separately packaged existence theorem.

**Weakest slice.** A **global abelian reciprocity map plus open-subgroup/ray
class functoriality** is enough for the downstream solvable-extension trick;
the full all-number-fields topological isomorphism is stronger than any single
consumer.  Local CFT alone does not suffice.

**Size / edges / risks.** **XL** to prove; **L** as an assumed interface.
Edges: item 1 → item 3 (explicit `\uses`), item 3 → item 4 → item 5, and the
existing idele substrate (item 9) → item 3.  Risks are the quotient topology and
profinite component notation, global product formula, and matching the
repository's finite-adele objects with the appendix's full adeles.

**Reference route.** Local Artin maps → ideles and the product formula → the
global Artin reciprocity isomorphism is the standard Neukirch/Milne sequence
**(literature-verify)**.

### 4. Skinner--Wiles solvable-extension / prescribed-local-data trick

**Citations.** `blueprint/src/chapter/chtopbestiary.tex:88-94` states that for
finite local Galois data (L_v/K_v) there is a finite **solvable** global
Galois extension (L/K) with those completions, and that (L) can be made
linearly disjoint from a prescribed finite extension.  It has the explicit
`\uses{global_class_field_theory}` edge at `:90`.  The assumptions README
repeats this target at `FLT/Assumptions/README.md:36-37`.

> “Then there is a finite solvable Galois extension $L/K$ ... Moreover, if
> $K^{\\avoid}/K$ is any finite extension then we can choose $L$ to be
> linearly disjoint from $K^{\\avoid}$.” (`chtopbestiary.tex:90-93`)

**Needs.** The finite-place local matching theorem, solvability of the global
Galois group, and linear-disjointness control.  A proof needs more than merely
the existence of one abelian extension: it needs a finite ray-class/open
subgroup construction and a solvable tower (the exact theorem-strength route
is **literature-verify**).  Local CFT alone is insufficient; global
reciprocity plus a finite existence/disjointness package is sufficient.

**Weakest slice.** The best implementation seam is a single **narrow global
solvable-extension axiom/API** with exactly the displayed inputs/outputs.  It
can be consumed without formalising the entire global reciprocity isomorphism.

**Size / edges / risks.** **S** to state as an assumption, **L–XL** to prove.
Edges: item 3 → item 4 → item 5; item 4 also supplies the formalizable
assumption named in the README.  Risks: “solvable” versus “successive cyclic”
towers, local-algebra versus field-isomorphism equality, and the disjointness
clause; all are currently `notready` in the blueprint.

**Reference route.** Ray-class fields/open subgroups, local specification,
then a solvable tower and disjointness argument is the standard CFT existence
route **(literature-verify)**.

### 5. Modularity-lifting theorem's CFT boundary

**Citations.** `blueprint/src/chapter/ch04overview.tex:66-77` states the
modularity-lifting theorem and lists `Skinner_Wiles_CFT_trick` among its
dependencies at `:68-72`; `:79` says the theorem is far from stated in Lean.

> `\\uses{Skinner_Wiles_CFT_trick,local_galois_coh_dim_two,...}`
> (`ch04overview.tex:68-72`).

**Needs.** From CFT, only item 4's solvable-extension/trick interface.  The
other listed dependencies are local Galois cohomology, automorphic
representation theory, adeles, and Moret--Bailly; they are not additional CFT
reciprocity requirements in the cited dependency list.

**Weakest slice.** Item 4 as an axiom/API; no need to expose the full global
Artin isomorphism to the modularity-lifting consumer.  Local CFT alone does
not supply this edge.

**Size / edges / risks.** The theorem itself is **XL**; its CFT slice is **S**
if item 4 is assumed, **L–XL** if item 4 is proved.  Edge item 4 → theorem.
Risk: the surrounding theorem is not formalised, so the eventual statement
may reveal additional local/global character data not visible in this
blueprint placeholder.

### 6. Potential-modularity strategy's unspecified global-CFT uses

**Citations.** `blueprint/src/chapter/ch04overview.tex:21-33` says the first
potential-modularity claim uses “several nontrivial results in global class
field theory,” alongside Moret--Bailly, Jacquet--Langlands, induced modularity,
and modularity lifting.  The proof strategy later invokes Moret--Bailly and
the lifting theorem at `:93-98`.

> “several nontrivial results in global class field theory”
> (`ch04overview.tex:27-32`).

**Needs.** The source does not identify which global CFT theorems are meant.
The only concrete CFT theorem wired elsewhere is item 4.  Therefore the
minimum defensible slice is item 4 plus whatever abelian/ray-class character
construction the eventual Moret--Bailly/potential-modularity formalisation
actually exposes; the exact boundary is **literature-verify**.

**Weakest slice / size / risks.** Treat as **L–XL**, with item 3 and item 4 as
candidate dependencies.  Do not commit to “full CFT” until the proof is
expanded: the prose is currently underspecified.  Risk is the largest CFT
scope uncertainty in the repo.

### 7. Cyclic base change: solvable extension as input, not CFT output

**Citations.** The blueprint says cyclic base change and image classification
are needed at `chtopbestiary.tex:210-214`; the Lean statement documents a
finite solvable (E/F) at `FLT/GaloisRepresentation/Automorphic.lean:109-125`
and requires `[IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)]` at `:127-133`.

> “Let `E/F` be a finite solvable extension ...” (`Automorphic.lean:112`) and
> `[Algebra F E] [IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)]`
> (`Automorphic.lean:131-133`).

**Needs.** A supplied finite Galois extension and its solvability/tower API,
plus the very large automorphic/base-change theorem.  The statement does not
ask CFT to construct (E), and no reciprocity theorem is referenced.

**Weakest slice.** **No CFT at all** once (E/F) is supplied: finite-extension
and solvable-group theory suffices.  If a caller needs to manufacture (E)
with prescribed local behavior, use item 4's narrow global solvable-extension
API, not the whole of item 3.

**Size / edges / risks.** The base-change theorem is **XL** (independent of CFT
size); its CFT contribution is **S** only when extension construction is
required.  Edge item 4 → (optional field-construction layer) → cyclic
base-change application.  Risk: confusing the theorem's solvability input
with a proof of existence; the current Lean declaration is `sorry` at `:184`.

### 8. Poitou--Tate / global Tate duality (planned consumer)

**Citations.** The appendix says “We also need Poitou-Tate duality” at
`chtopbestiary.tex:96`; the assumptions README lists it at `:65-68`; and the
GL(0) file's commentary says Wiles used global Tate duality at
`FLT/GlobalLanglandsConjectures/GLzero.lean:22-27`.

> “We also need Poitou-Tate duality; I'll refrain from writing it down for
> now, because we don't even have Galois cohomology in Lean yet”
> (`chtopbestiary.tex:96`).

**Needs.** No formal theorem statement exists in this checkout.  A likely
boundary is local duality plus the local (H^2) invariant/Brauer map, Kummer
identifications, and the global reciprocity/product formula; the exact
minimal package is **literature-verify**.  It is not enough to have only the
idele topology, and it is not the same as the finite-group Tate-cohomology
file in Mathlib.

**Weakest slice.** For a Poitou--Tate consumer, expose a cohomological duality
interface (local invariant maps, Kummer sequence, global reciprocity law and
the long exact sequence) rather than all class-field existence theorems.
Local CFT alone is insufficient for the global sequence.

**Size / edges / risks.** **XL**.  It is parallel to item 4 and feeds the
Taylor--Wiles/global-duality portions of item 5; the exact edge is not encoded
in current Lean.  Risk: the sibling-map claim that this chapter already has a
CFT boundary is not verifiable here; the current repo has only placeholders.

### 9. Existing idele/adele topology substrate (support, not a CFT consumer)

**Citations.** `FLT/DedekindDomain/FiniteAdeleRing/LocalUnits.lean:75-117`
constructs local uniformisers and local units in the finite adele-ring units.
The production umbrella imports this module at `FLT/FLT.lean:18-24` and the
finite-adele Mathlib layer at `:147-150`.

> “`localUniformiser v` is an adele which is 1 at all finite places except
> `v`” (`LocalUnits.lean:75-76`) and “`localUnit K α` ... is the finite idele
> which is `α` at `v` and `1` elsewhere” (`LocalUnits.lean:113-117`).

**Needs / weakest slice.** It needs only restricted products, valuations,
adic completions, and topology.  It uses no reciprocity, Brauer invariant, or
Kummer theorem, so its weakest CFT slice is **none**.  It is nevertheless the
natural data layer for item 3's idele class group.

**Size / edges / risks.** Existing support is **M** (with more work needed for
the full idelic quotient).  Edge: substrate → item 3.  Risk: finite adeles are
well represented, while the global theorem in the blueprint uses full adeles
and a profinite component quotient.

## Mathlib coverage summary

### Present and reachable in the checked-out dependency

* **Local-field/valuation infrastructure, not local CFT.** Mathlib's
  `NumberTheory/LocalField/Basic.lean:8-19` imports valuative/topological
  modules and defines non-archimedean local fields; its class and inferred
  structures are listed at `:25-38`.  FLT reaches it through the Tate-curve
  files, e.g. `FLT/KnownIn1980s/EllipticCurves/TateCurve.lean:8-13`.
  There is no local Artin reciprocity theorem in that file.
* **Galois and abelian-extension API.** `Mathlib/FieldTheory/Galois/Abelian.lean:8-26`
  defines `IsAbelianGalois`; FLT reaches `FieldTheory/Galois.Abelian` through
  `Mathlib/NumberTheory/Cyclotomic/Basic.lean:8-12`, which is imported by
  `FLT/GaloisRepresentation/Cyclotomic.lean:8-10`.  This is field/Galois
  structure, not class-field reciprocity or an existence theorem.
* **Kummer theory as an optional Mathlib file.**
  `Mathlib/FieldTheory/KummerExtension.lean:8-25` contains cyclic Kummer
  extension results.  The FLT production import list has primitive-root and
  cyclotomic imports (`FLT/AutomorphicForm/Stuff.lean:8-15`,
  `FLT/GaloisRepresentation/Cyclotomic.lean:8-10`) but no direct
  `KummerExtension`/`RootsOfUnity.Lemmas` import; the only broad test import is
  `FLTTest/MathlibCompatibility.lean:6-7` (`import Mathlib`, then `import FLT`).
  Thus Kummer is available in the installed Mathlib package/test environment,
  but is not a CFT implementation and is not a production FLT dependency by
  direct import.
* **Finite adeles/restricted-product units.** Mathlib's
  `RingTheory/DedekindDomain/FiniteAdeleRing.lean:8-20` defines finite adeles
  as restricted products, and imports restricted-product units at `:10-11`.
  FLT adds local-unit constructors as cited in item 9.  This covers topology
  and algebraic containers, not the idele class group or Artin map.
* **Continuous-cohomology foundations.** FLT's own
  `FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean:15-35`
  develops continuous cochain complexes/cohomology, and its cup-product file
  documents the cup pairing at `:17-35`.  These are useful prerequisites for
  Poitou--Tate, but no local/global duality theorem is present.
* **Finite-group Tate cohomology.** Mathlib's
  `RepresentationTheory/Homological/TateCohomology/Basic.lean:14-19,31-38`
  defines Tate cohomology for finite groups; its note at `:49-50` attributes
  the file to a ClassFieldTheory workshop.  This is not local Tate duality,
  global Tate duality, or Poitou--Tate.
* **Brauer group definitions only.**
  `Mathlib/Algebra/BrauerGroup/Defs.lean:14-25,38-47,97-99` defines central
  simple algebras, Brauer equivalence, and the quotient `BrauerGroup`, with
  TODOs for the group law/functoriality.  No local invariant map,
  (\operatorname{Br}(K_v)\simeq\mathbb Q/\mathbb Z), or Hasse invariant theorem
  is present in the searched source.
* **Class groups/class numbers and infinite Galois theory.** Mathlib has the
  ideal class group (`RingTheory/ClassGroup/Basic.lean:12-27`), class numbers
  (`NumberTheory/NumberField/ClassNumber.lean:14-25`), and the fundamental
  theorem of infinite Galois theory (`FieldTheory/Galois/Infinite.lean:14-20,
  37-50`).  These are useful ingredients but not ray-class existence or CFT.

### Missing from the reachable source

The checked-out Mathlib tree has no filename matching class-field/CFT/Lubin--
Tate/Artin-reciprocity, and a content grep for “Lubin”, “local reciprocity”,
“Artin map”, “class field theory”, and “Hasse invariant” returned no hits.
The lake manifest lists Mathlib and ordinary support packages only
(`lake-manifest.json:3-13,14-103`); no separate ClassFieldTheory package is
installed.  Therefore the following are missing and would have to be added or
axiomatized for this campaign:

1. local Artin reciprocity (including the Lubin--Tate proof/API);
2. global idelic reciprocity with local compatibility;
3. ray-class/open-subgroup existence and the solvable/disjoint local-global
   extension theorem;
4. local/global Brauer invariant maps and Brauer--Hasse--Noether
   **(literature-verify)**;
5. Kummer exact-sequence/cohomological identifications as used by duality
   **(literature-verify)**;
6. Poitou--Tate/global Tate duality.

## Overall size verdict and recommended slice ordering

The cheapest useful campaign is not “formalise all of CFT first.”  Order the
slices as follows:

The standard composition to keep in mind is **local reciprocity → ideles and
global reciprocity → ray-class/open-subgroup existence → the solvable/disjoint
extension interface**, with **local invariants/Brauer/Kummer → global Tate or
Poitou--Tate duality** as a parallel cohomological branch
**(literature-verify)**.  Items 2, 4, and 7 can stop at the narrow seams in
that graph; items 3, 6, and 8 are the broad/full-theory branch.

1. **S/M:** define the exact local inertia-character interface for item 2 and
   connect it to the existing `localTameAbelianInertiaGroup` API.
2. **S:** introduce the item-4 solvable-extension statement (including local
   algebra matching and linear disjointness) as a named assumption, matching
   `Assumptions/README.md:36-37`.  This immediately unblocks the CFT edge of
   modularity lifting without committing to a global proof.
3. **M:** finish the finite-idele/topological quotient interfaces using the
   existing finite-adeles/restricted-product code (item 9).
4. **L–XL:** develop global reciprocity only if the expanded potential-
   modularity proof (item 6) needs more than the item-4 API.  Build it on local
   reciprocity, then add ray-class/open-subgroup existence.
5. **XL, parallel track:** formalise the local invariant/Brauer/Kummer and
   Poitou--Tate interfaces needed by the Taylor--Wiles/global-duality path.

In short: items 2 and 4 are cheap/narrow seams; item 7 needs no CFT when its
solvable tower is supplied; items 3, 6, and 8 require broad or full theory.
The global CFT theorem is an XL proof target but need not be exposed to every
consumer if the narrow item-4 assumption is accepted.
