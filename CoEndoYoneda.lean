import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Category.KleisliCat

/-

Given a presheaf `C ⥤ Type u` *and* a functor of type `Type u ⥤ C`
they can be composed to an endofunctor `C ⥤ C`.

For example, a presheaf `CYF X` and a functor `Φ` as `CYF X ⋙ Φ`

The existence of such a functor of type `Type u ⥤ C` is the first
requirement of `class FunctionalCategory` modeled as
- `Φ : Type u ⥤ C`.

`class FunctionalCategory` also requires the existence of
`Monad`-like natural transformations for global-like values
together with a left unit law modeled as
- `γμ : (GEF_def Φ ⋙ GEF_def Φ) ⟶ GEF_def Φ`
- `γη : 𝟭 _ ⟶ GEF_def Φ`
- `γ_left_unit : ∀ (X : C), γη.app ((GEF_def Φ).obj X) ≫ γμ.app X = 𝟙 ((GEF_def Φ).obj X)`
where
- `def GEF_def {C : Type (u + 1)} [LargeCategory.{u} C] (Φ : Type u ⥤ C) : C ⥤ C`
is an endofunctor constructing `Φ`-related global values.

I could have defined a `GlobalMonad` but I did not do it
because only `γ_left_unit` is required
(`γ_right_unit` and `γ_assoc` are not needed).

-/

set_option mathlib.tactic.category.grind true

namespace typesAndFunctionsCoEndoYoneda

open CategoryTheory
open Opposite

universe u

-- CoYoneda `Functor` for `X`
def CYF {C : Type (u + 1)} [Category.{u} C] (X : C) : C ⥤ Type u :=
  coyoneda.obj (op X)

-- the specific `typesCoEndoYonedaEquiv` equivalence for `Type u` endofunctors
-- is just a special case of the general `coyonedaEquiv` equivalence
--
-- a natural question is for what kind of categories `C` is there a
-- general `coEndoYonedaEquiv` equivalence for `C` endofunctors
--
def typesCoEndoYonedaEquiv {F : Type u ⥤ Type u} (X : Type u) : (CYF X ⟶ F) ≃ F.obj X :=
  coyonedaEquiv

end typesAndFunctionsCoEndoYoneda


namespace typesAndKleisliIdFunctionsCoEndoYoneda

open typesAndFunctionsCoEndoYoneda

universe u

open CategoryTheory

def typeToKleisliId : Type u ⥤ KleisliCat Id where
  obj X := KleisliCat.mk Id X
  map {X Y} (f : X ⟶ Y) := fun x => (f x : Id Y)
  map_id _ := rfl
  map_comp _ _ := rfl

def kleisliIdToType : KleisliCat Id ⥤ Type u where
  obj X := X
  map {X Y} (f : X ⟶ Y) := TypeCat.ofHom (fun (x : X) => (f x : Y))
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

def kleisliIdEquivalence : Type u ≌ KleisliCat Id where
  functor := typeToKleisliId
  inverse := kleisliIdToType
  unitIso := NatIso.ofComponents
    (fun X => {
      hom := TypeCat.ofHom (fun (x : X) => x)
      inv := TypeCat.ofHom (fun (x : X) => x)
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl
    })
    (by intros X Y f; ext x; rfl)
  counitIso := NatIso.ofComponents
    (fun X => {
      hom := fun (x : X) => (x : Id X)
      inv := fun (x : X) => (x : Id X)
      hom_inv_id := rfl
      inv_hom_id := rfl
    })
    (by intros X Y f; rfl)
  functor_unitIso_comp X := by rfl

def typesAndKleisliIdFunctionsCoEndoYonedaEquiv
  {F : KleisliCat Id ⥤ Type u} (X : KleisliCat Id) : (CYF X ⟶ F) ≃ F.obj X :=
    coyonedaEquiv

end typesAndKleisliIdFunctionsCoEndoYoneda

namespace CoEndoYoneda

open CategoryTheory
open Opposite

universe u

-- CoYoneda `Functor` for `X`
def CYF {C : Type (u + 1)} [LargeCategory.{u} C] (X : C) : C ⥤ Type u :=
  coyoneda.obj (op X)

-- CoYoneda `EndoFunctor` for `Φ : Type u ⥤ C` and `X`
def CYEF_def {C : Type (u + 1)} [LargeCategory.{u} C] (Φ : Type u ⥤ C) (X : C) : C ⥤ C :=
  CYF X ⋙ Φ

-- Global `EndoFunctor` definition for `Φ : Type u ⥤ C` (`X` being `PUnit`)
def GEF_def {C : Type (u + 1)} [LargeCategory.{u} C] (Φ : Type u ⥤ C) : C ⥤ C :=
  CYEF_def Φ (Φ.obj PUnit)

-- Global elements for `Φ : Type u ⥤ C` are morphisms of type `Φ.obj PUnit ⟶ X`
def G {C : Type (u + 1)} [LargeCategory.{u} C] (Φ : Type u ⥤ C) (X : C) : Type u :=
  Φ.obj PUnit ⟶ X

-- `FunctionalCategory` is supposed to specify programs
-- bot pure programs (without side-effects) and impure programs (with side-effects)
-- but, ... , see later
class FunctionalCategory (C : Type (u + 1)) extends LargeCategory.{u} C where
  -- Functional Functor
  Φ : Type u ⥤ C

  -- Global Multiplication
  γμ : (GEF_def Φ ⋙ GEF_def Φ) ⟶ GEF_def Φ

  -- Global Unit
  γη : 𝟭 _ ⟶ GEF_def Φ

  -- Global Multiplication associativity law is not (yet) needed
  -- γ_assoc :
  --   ∀ (X : C), (GEF_def Φ).map (γμ.app X) ≫ γμ.app X = γμ.app ((GEF_def Φ).obj X) ≫ γμ.app X

  -- Right Global Unit law is not (yet) needed
  -- γ_right_unit :
  --   ∀ (X : C), (GEF_def Φ).map (γη.app X) ≫ γμ.app X = 𝟙 ((GEF_def Φ).obj X)

  -- Left Global Unit law
  γ_left_unit : ∀ (X : C), γη.app ((GEF_def Φ).obj X) ≫ γμ.app X = 𝟙 ((GEF_def Φ).obj X)

  -- Functional `Functor` `map`
  -- Note that we are into the `ConcreteCategory` realm now via `TypeCat.ofHom`
  φ {X Y : Type u} (f : X → Y) : Φ.obj X ⟶ Φ.obj Y := Φ.map (TypeCat.ofHom f)

  -- Functional `Functor` `map` equality
  -- Note that we are into the `ConcreteCategory` realm now via `TypeCat.ofHom`
  φ_eq : ∀ {X Y : Type u} (f : X → Y), φ f = Φ.map (TypeCat.ofHom f) := by
    intros
    rfl

  -- relating `γη` and `φ`
  -- (also involves `Φ.obj`, recall that `φ` is defined in terms of `Φ.map`)
  γη_φ : ∀ (X : Type u), γη.app (Φ.obj X) = φ (fun x => φ (fun _ => x)) := by
    intros
    rfl

  -- not really needed because not all `μ` and `η` laws are needed
  -- GM : Monad C := {
  --   toFunctor := GEF_def Φ
  --   μ := γμ
  --   η := γη
  --   assoc := γ_assoc
  --   left_unit := γ_left_unit
  --   right_unit := γ_right_unit
  -- }

open FunctionalCategory

-- CoYoneda EndoFunctor
def CYEF {C : Type (u + 1)} [FunctionalCategory C] (X : C) : C ⥤ C :=
  CYEF_def Φ X

-- Global EndoFunctor
-- `grind` complains about `left_inverse` (see later) when this is a `def`
abbrev GEF {C : Type (u + 1)} [FunctionalCategory C] : C ⥤ C :=
  GEF_def Φ


/-

For `C = Type u`, the world of "pure programs without side-effects (functions)"
there is a trivial instance modeled as
- `instance typesFunctionalCategory : FunctionalCategory (Type u) where`
-   `Φ := 𝟭 (Type u)`
-   ...
(for trivial definitions of the other declarations : see code).

But what about the programming world that consist both of
"pure programs without side-effects" and
"impure programs with side-effects"?

My idea was to formulate a CoEndoYoneda equivalence for endofunctors
that could play a role in the programming world, and it turned out
that the `FunctionalCategory` requirements were sufficient to prove
that CoEndoYoneda equivalence.

The formulation is modeled as
- `def coEndoYonedaEquiv {F : C ⥤ C} {X : C} : (CYEF X ⟶ (F ⋙ GEF)) ≃ Global ((F ⋙ GEF).obj X)`
where
- `def Global : C → Type u := G Φ`
where
- `def G {C : Type (u + 1)} [LargeCategory.{u} C] (Φ : Type u ⥤ C) (X : C) : Type u`
model `Φ`-related global values

The proof of the equivalence uses
- `def τx2ggfx {F : C ⥤ C} {X : C} (τx : CYEF X ⟶ F ⋙ GEF) : Global ((F ⋙ GEF).obj X)`
modeling a function that
given a natural transformation argument of type `CYEF X ⟶ (F ⋙ GEF)`.
Yields a "global global value" result of type `Global ((F ⋙ GEF).obj X)`

and

- `def ggfx2τx {F : C ⥤ C} {X : C} (ggfx : Global (GEF.obj (F.obj X))) : CYEF X ⟶ (F ⋙ GEF)`
modeling a function that
given a "global global value" argument of type `Global (GEF.obj (F.obj X))`
yields a natural transformation result of type `CYEF X ⟶ (F ⋙ GEF)`.

The proof of the equivalence also uses
- `theorem left_inverse {F : C ⥤ C} {X : C} (τx : CYEF X ⟶ (F ⋙ GEF)) :`
    `τx = ggfx2τx (φ (fun _ => 𝟙 X) ≫ τx.app X)`

and

- `theorem right_inverse {F : C ⥤ C} {X : C} (ggfx : Global ((F ⋙ GEF).obj X)) :`
    `ggfx = (φ (fun _ => 𝟙 X)) ≫ (ggfx2τx ggfx).app X`

Both `theorem`s apply `φ` (defined as `Φ.map` using `TypeCat.ofHom`) to `fun _ => 𝟙 X`.
For those who know about the classic `coyoneda` equivalence, should not come as a surprise.

We also prove a less substantial (and less elegant) lemma that does not use `γμ`.

The formulation is modeled as
- `theorem coEndoYonedaLemma {F : C ⥤ C} {X : C} (τx : CYEF X ⟶ F) :`
    `τx2γτx τx =`
      `gfx2τx (φ (fun _ => 𝟙 X) ≫ τx.app X)`

It also applies  `φ` defined to `fun _ => 𝟙 X`
(for more details : see code).

We could have proved a corresponding equivalence as well.

But ... there is bad news and good news!

First the bad news.

Trying to define a `FunctionalCategory` instance for `KleisliCat M` for a monad `M`
turned out not to be possible.

So my `coEndoYonedaEquiv` is not generally useful for the programming world,
only for the pure programming world, as far as `KleisliCat M` is concerned,
where pureness then boils down to monad computation referential transparancy,
cfr. expression evaluation referential transparancy.

Next the good news (every disadvantage has an advantage).

`class FunctionalCategory` actually *classifies* the property
of being pure, without side-effects in `KleisliCat M`
in a categorical way, because it forces equality
`mz >>= fun z => pure (pure z) = pure mz`.

The constraint imposed by `γη.naturality` on morphisms demands that
binding `pure` twice to `mz` is exactly the same as applying `pure` to `mz`.

If a `Monad` satisfies this purity constraint
(which is required to instantiate `FunctionalCategory` class via `KleisliCat`),
then its shape functor evaluated at `PUnit` is a `Subsingleton`.

This means `M` is a trivial `Monad` (e.g. `Identity`, `Truncation`, or `Terminal`).

We have formally verified this rejection for six standard computational monads in `PurityExamples.lean`:
`Option`, `List`, `Reader R`, `Writer W`, `State S`, and `Cont R`.
Satisfying the EnforcesPurity constraint for these monads either leads to a direct logical contradiction (as with `Option` and `List`) or mathematically forces their underlying parameters to be trivial (e.g. forcing the state type or the reader environment to be a `Subsingleton`).

Formalizing the requirement:
if `KleisliCat M` admits a `FunctionalCategory` structure under the canonical embedding
then `M` is mathematically forced to satisfy the `EnforcesPurity` constraint.

In a nutshell, as a side-effect (no pun intended (!)) I proved,
in the `KleisliCat M` world the following theorem :

*Referential transparancy is exactly the condition required for
a computational context to admit a global CoEndoYoneda equivalence*
(for more details : see code).

-/

-- trivial `FunctionalCategory` instance
instance typesFunctionalCategory : FunctionalCategory (Type u) where
  Φ := 𝟭 (Type u)

  γη := {
    app := fun X => (𝟭 (Type u)).map (↾(fun x => ↾(fun _ => x)))
    naturality := fun X Y f => by
      ext
      rfl
  }

  γμ := {
    app :=
      fun X => (𝟭 (Type u)).map (↾(fun (f : PUnit ⟶ PUnit ⟶ X) => ↾(fun pu => f pu pu)))
    naturality := fun X Y f => by
      ext
      rfl
  }

  γ_left_unit := fun _ => by
    rfl

section LessSubstantialLemma

variable {C : Type (u + 1)} [FunctionalCategory C]

def Global : C → Type u := G Φ

-- `Functor` composition law for `φ`
-- Note that we are into the `ConcreteCategory` realm now via `TypeCat.ofHom`
@[simp]
theorem φ_comp {X Y Z : Type u} (f : X → Y) (g : Y → Z) :
    φ f ≫ φ g = (φ (C := C) (fun x => g (f x)) : Φ.obj X ⟶ Φ.obj Z) := by
  have h1 : φ (C := C) f = Φ.map (TypeCat.ofHom f) := φ_eq f
  have h2 : φ (C := C) g = Φ.map (TypeCat.ofHom g) := φ_eq g
  have h3 : φ (C := C) (fun x => g (f x)) = Φ.map (TypeCat.ofHom (fun x => g (f x))) := φ_eq _
  rw [h1, h2, h3, ← Φ.map_comp]
  rfl

-- `PUnit` identity law for `φ`
-- Note that `PUnit` has only one value
@[simp]
theorem φ_pu_id (pu : PUnit) : φ (C := C) (fun _ => pu) = 𝟙 (Φ.obj PUnit) := by
  have h_pu_id : (fun _ => pu) = id := rfl
  have h_id_eq : φ (C := C) id = Φ.map (𝟙 PUnit) := by exact φ_eq id
  exact Eq.trans (congr_arg φ h_pu_id) (Eq.trans h_id_eq (Φ.map_id PUnit))

-- Equation relating `(CYEF Z).map` and `φ`
@[simp]
theorem CYEF_map_eq_φ {Z X Y : C} (f : X ⟶ Y) : (CYEF Z).map f = φ (. ≫ f) := by
  dsimp only [CYEF, CYEF_def, CYF, coyoneda, yoneda, Functor.comp_obj, Functor.comp_map]
  exact (φ_eq (. ≫ f)).symm

-- Equation relating `GEF.map` and `φ`
@[simp]
theorem GF_map_eq_φ {X Y : C} (f : X ⟶ Y) : GEF.map f = φ (. ≫ f) :=
  CYEF_map_eq_φ f

@[simps]
def τx2γτx {F : C ⥤ C} {X : C} (τ : CYEF X ⟶ F) :
  CYEF X ⟶ (F ⋙ GEF)
where
  app Y := τ.app Y ≫ γη.app (F.obj Y)
  naturality _ _ h := by
    dsimp
    have h_nat := γη.naturality (F.map h)
    dsimp at h_nat
    erw [τ.naturality_assoc, h_nat]
    rw [Category.assoc]
    rfl

-- given a global argument of type `Global (F.obj X)`
-- yields a natural transformation result of type `CYEF X ⟶ (F ⋙ GEF)`
@[simps]
def gfx2τx {F : C ⥤ C} {X : C} (gfx : Global (F.obj X)) :
    CYEF X ⟶ (F ⋙ GEF) where
  app Y := φ (gfx ≫ F.map .)
  naturality _ _ h := by
    change
      Φ.map ((CYF X).map h) ≫ φ _ =
        φ _ ≫ Φ.map ((CYF (Φ.obj PUnit)).map (F.map h))
    rw [φ_eq, φ_eq]
    rw [← Φ.map_comp, ← Φ.map_comp]
    congr 1
    ext f
    change
      gfx ≫ F.map (f ≫ h) =
        (gfx ≫ F.map f) ≫ F.map h
    rw [F.map_comp, Category.assoc]

-- `τx2γτx τx` with `τx` of type `CYEF X ⟶ F`
-- can be defined in terms of `φ (fun _ => 𝟙 X) ≫ τx.app X`
theorem coEndoYonedaLemma {F : C ⥤ C} {X : C} (τx : CYEF X ⟶ F) :
  τx2γτx τx =
    gfx2τx (φ (fun _ => 𝟙 X) ≫ τx.app X) := by
  ext Y
  dsimp [τx2γτx, gfx2τx]
  erw [γη.naturality (τx.app Y)]
  erw [γη_φ (X ⟶ Y)]
  erw [GF_map_eq_φ (τx.app Y)]
  erw [φ_comp]
  congr 1
  ext f
  dsimp only [CYEF, CYEF_def, GEF, GEF_def, CYF, coyoneda, yoneda, Functor.comp_obj, Functor.comp_map]
  have step1 :
    (φ (fun _ => 𝟙 X) ≫ τx.app X) ≫ F.map f =
      φ (X := PUnit) (Y := X ⟶ X) (fun _ => 𝟙 X) ≫ (τx.app X ≫ F.map f) :=
        Category.assoc _ _ _
  have step2 :
    φ (fun _ => 𝟙 X) ≫ (τx.app X ≫ F.map f) = φ (fun _ => 𝟙 X) ≫ ((CYEF X).map f ≫ τx.app Y) :=
      congr_arg
        (φ (C := C) (X := PUnit) (Y := X ⟶ X) (fun _ => 𝟙 X) ≫ .) (τx.naturality f).symm
  have step3 :
    φ (fun _ => 𝟙 X) ≫ ((CYEF X).map f ≫ τx.app Y) =
      (φ (X := PUnit) (Y := X ⟶ X) (fun _ => 𝟙 X) ≫ (CYEF X).map f) ≫ τx.app Y :=
        (Category.assoc _ _ _).symm
  have step4Helper :
    φ (fun _ => 𝟙 X) ≫ (CYEF X).map f =
      φ (X := PUnit) (Y := X ⟶ Y) (fun _ => f) := by
        erw [CYEF_map_eq_φ f]
        have h_φ : φ (fun _ => 𝟙 X) ≫ φ (. ≫ f) =
          φ (C := C) (X := PUnit) (Y := X ⟶ Y) (fun _ => 𝟙 X ≫ f) :=
            φ_comp (fun _ => 𝟙 X) (. ≫ f)
        erw [h_φ]
        congr 1
        ext _
        exact Category.id_comp f
  have step4 :
    (φ (fun _ => 𝟙 X) ≫ (CYEF X).map f) ≫ τx.app Y = φ (fun _ => f) ≫ τx.app Y :=
      congr_arg (. ≫ τx.app Y) step4Helper
  exact (Eq.trans step1 (Eq.trans step2 (Eq.trans step3 step4))).symm

end LessSubstantialLemma

section CoEndoYonedaEquivalence

variable {C : Type (u + 1)} [FunctionalCategory C]

-- given a natural transformation argument of type `CYEF X ⟶ (F ⋙ GEF)`
-- yields a global global result of type `Global ((F ⋙ GEF).obj X)`
def τx2ggfx {F : C ⥤ C} {X : C} (τx : CYEF X ⟶ F ⋙ GEF) :
  Global ((F ⋙ GEF).obj X) :=
    let ggfx := φ (fun _ => 𝟙 X) ≫ τx.app X
    ggfx

-- given a global global argument of type `Global (GEF.obj (F.obj X))`
-- yields a natural transformation result of type `CYEF X ⟶ (F ⋙ GEF)`
--
-- TODO : type system complains when using `Global ((F ⋙ GEF).obj X)` (?)
--
@[simps]
def ggfx2τx
  {F : C ⥤ C} {X : C} (ggfx : Global (GEF.obj (F.obj X))) : CYEF X ⟶ (F ⋙ GEF) :=
    let τx : CYEF X ⟶ F ⋙ GEF := {
      app Y := φ (ggfx ≫ (F ⋙ GEF).map .) ≫ γμ.app (F.obj Y)
      naturality _ _ h := by
        dsimp only [CYEF, GEF, CYEF_def, GEF_def, Functor.comp_map, Functor.comp_obj]
        erw [Category.assoc]
        erw [← γμ.naturality (F.map h)]
        erw [← Category.assoc, ← Category.assoc]
        congr 1
        change
          Φ.map ((CYF X).map h) ≫ φ _ = φ _ ≫ Φ.map ((CYF (Φ.obj PUnit)).map (GEF.map (F.map h)))
        rw [φ_eq, φ_eq]
        rw [← Φ.map_comp, ← Φ.map_comp]
        congr 1
        ext f
        change ggfx ≫ GEF.map (F.map (f ≫ h)) = (ggfx ≫ GEF.map (F.map f)) ≫ GEF.map (F.map h)
        rw [F.map_comp, GEF.map_comp, Category.assoc]
    }
    τx

-- `τx` of type `CYEF X ⟶ (F ⋙ GEF)` equals `(ggfx2τx ∘ τx2ggfx) τx`
theorem left_inverse {F : C ⥤ C} {X : C} (τx : CYEF X ⟶ (F ⋙ GEF)) :
    τx = (ggfx2τx ∘ τx2ggfx) τx := by
  ext Y
  dsimp [ggfx2τx]
  have h_stepB :
    τx.app Y =
      (γη.app ((CYEF X).obj Y) ≫ GEF.map (τx.app Y)) ≫ γμ.app (F.obj Y) := by
        grind [γ_left_unit (F.obj Y), γη.naturality (τx.app Y)]
  have h_γη_φ : γη.app ((CYEF X).obj Y) = φ (fun f => φ (fun _ => f)) := γη_φ (X ⟶ Y)
  have h_stepC : τx.app Y =
    (φ (fun f => φ (C := C) (X := PUnit) (Y := X ⟶ Y) (fun _ => f)) ≫
      GEF.map (τx.app Y)) ≫
        γμ.app (F.obj Y) :=
          Eq.trans h_stepB
            (congr_arg (fun g => (g ≫ GEF.map (τx.app Y)) ≫ γμ.app (F.obj Y)) h_γη_φ)
  have h_stepD : τx.app Y =
    (φ (fun g => φ (fun _ => g)) ≫ φ (. ≫ τx.app Y)) ≫ γμ.app (F.obj Y) :=
      Eq.trans h_stepC
        (congr_arg (fun g => (φ (fun f => φ (fun _ => f)) ≫ g) ≫
          γμ.app (F.obj Y)) (GF_map_eq_φ (τx.app Y)))
  have h_φ_comp :
    φ (fun f => φ (fun _ => f)) ≫ φ (. ≫ τx.app Y) =
      φ (C := C) (fun f => φ (X := PUnit) (fun _ => f) ≫ τx.app Y) :=
        φ_comp _ _
  have h_stepE :
    τx.app Y =
      φ (fun f => φ (fun _ => f) ≫ τx.app Y) ≫ γμ.app (F.obj Y) :=
        Eq.trans h_stepD (congr_arg (. ≫ γμ.app (F.obj Y)) h_φ_comp)
  have h_inner_eq :
    φ (fun f => φ (fun _ => f) ≫ τx.app Y) =
      φ (C := C) ((φ (X := PUnit) (fun _ => 𝟙 X) ≫ τx.app X) ≫ (F ⋙ GEF).map .) := by
    congr 1
    ext f
    dsimp only
      [CYEF, CYEF_def, GEF, GEF_def, CYF, coyoneda, yoneda, Functor.comp_obj, Functor.comp_map]
    have step1 :
      (φ (fun _ => 𝟙 X) ≫ τx.app X) ≫ (F ⋙ GEF).map f =
        φ (X := PUnit) (fun _ => 𝟙 X) ≫ (τx.app X ≫ (F ⋙ GEF).map f) := Category.assoc _ _ _
    have step2 :
      φ (fun _ => 𝟙 X) ≫ (τx.app X ≫ (F ⋙ GEF).map f) =
        φ (fun _ => 𝟙 X) ≫ ((CYEF X).map f ≫ τx.app Y) :=
          congr_arg (φ (X := PUnit) (fun _ => 𝟙 X) ≫ .) (τx.naturality f).symm
    have step3 :
      φ (fun _ => 𝟙 X) ≫ ((CYEF X).map f ≫ τx.app Y) =
        (φ (X := PUnit) (fun _ => 𝟙 X) ≫ (CYEF X).map f) ≫ τx.app Y := (Category.assoc _ _ _).symm
    have step4Helper :
      φ (fun _ => 𝟙 X) ≫ (CYEF X).map f =
        φ (X := PUnit) (fun _ => f) := by
          erw [CYEF_map_eq_φ f]
          have h_φ :
            φ (fun _ => 𝟙 X) ≫ φ (. ≫ f) =
              φ (C := C) (X := PUnit) (fun _ => 𝟙 X ≫ f) :=
                φ_comp (fun _ => 𝟙 X) (. ≫ f)
          erw [h_φ]
          congr 1
          ext _
          exact Category.id_comp f
    have step4 :
      (φ (fun _ => 𝟙 X) ≫ (CYEF X).map f) ≫ τx.app Y =
        φ (fun _ => f) ≫ τx.app Y := congr_arg (. ≫ τx.app Y) step4Helper
    exact (Eq.trans step1 (Eq.trans step2 (Eq.trans step3 step4))).symm
  have h_final :
    τx.app Y =
      φ (fun f => (φ (fun _ => 𝟙 X) ≫ τx.app X) ≫ (F ⋙ GEF).map f) ≫ γμ.app (F.obj Y) :=
        Eq.trans h_stepE (congr_arg (. ≫ γμ.app (F.obj Y)) h_inner_eq)
  exact h_final

-- relating `γμ` and `φ` (also involves `Φ.obj`)
-- (recall that `φ` is defined in terms of `Φ.map`)
theorem φ_γμ {X : C} (ggfx : Global (GEF.obj X)) :
    φ (fun (_ : PUnit) => ggfx) ≫ γμ.app X = ggfx := by
  have h_nat : ggfx ≫ γη.app (GEF.obj X) =
    γη.app (Φ.obj PUnit) ≫ GEF.map ggfx := γη.naturality ggfx
  erw [GF_map_eq_φ ggfx] at h_nat
  have h_γη : γη.app (Φ.obj PUnit) = φ (C := C) (fun pu => φ (fun _ => pu)) := γη_φ PUnit
  erw [h_γη] at h_nat
  have h_comp2 : φ (fun pu => φ (fun _ => pu)) ≫ φ (. ≫ ggfx) =
    φ (C := C) (Y := Global (GEF.obj X)) (fun pu => φ (fun _ => pu) ≫ ggfx) := φ_comp _ _
  erw [h_comp2] at h_nat
  have h_id_w : (fun pu => φ (fun _ => pu) ≫ ggfx) = (fun _ => ggfx) := by
    funext pu
    erw [φ_pu_id pu, Category.id_comp]
  have h_g_eta : ggfx ≫ γη.app (GEF.obj X) =
    φ (fun _ => ggfx) := by
      erw [h_id_w] at h_nat
      exact h_nat
  have h_left_unit : γη.app (GEF.obj X) ≫ γμ.app X = 𝟙 (GEF.obj X) := by
    exact γ_left_unit X
  have h_final : (ggfx ≫ γη.app (GEF.obj X)) ≫ γμ.app X =
    ggfx ≫ 𝟙 (GEF.obj X) := by
      erw [Category.assoc, h_left_unit]
  erw [Category.comp_id] at h_final
  erw [h_g_eta] at h_final
  exact h_final

-- `ggfx` of type `Global ((F ⋙ GEF).obj X)` equals `(τx2ggfx ∘ ggfx2τx) ggfx`
theorem right_inverse {F : C ⥤ C} {X : C} (ggfx : Global ((F ⋙ GEF).obj X)) :
    ggfx = (τx2ggfx ∘ ggfx2τx) ggfx := by
  change
    ggfx = φ (fun _ => 𝟙 X) ≫
      (φ (Y := Global (GEF.obj (F.obj X))) (ggfx ≫ (F ⋙ GEF).map .) ≫
        γμ.app (F.obj X))
  rw [← Category.assoc]
  have h1 :
    φ (fun _ => 𝟙 X) ≫ φ (Y := Global (GEF.obj (F.obj X))) (ggfx ≫ (F ⋙ GEF).map .) =
      φ (C := C) (X := PUnit) (Y := Global (GEF.obj (F.obj X)))
        (fun _ => ggfx ≫ (F ⋙ GEF).map (𝟙 X)) := φ_comp _ _
  rw [h1]
  have h2 :
    φ (Y := Global (GEF.obj (F.obj X))) (fun _ => ggfx ≫ (F ⋙ GEF).map (𝟙 X)) =
      φ (C := C) (X := PUnit) (fun _ => ggfx) := by grind
  rw [h2]
  exact (φ_γμ ggfx).symm

-- main equivalence
def coEndoYonedaEquiv {F : C ⥤ C} {X : C} : (CYEF X ⟶ (F ⋙ GEF)) ≃ Global ((F ⋙ GEF).obj X)
where
  toFun     := τx2ggfx
  invFun    := ggfx2τx
  left_inv  := fun τx => (left_inverse  τx).symm
  right_inv := fun τx => (right_inverse τx).symm

end CoEndoYonedaEquivalence

section PurityTheorem

open Functor

universe v

variable (M : Type v → Type v) [Monad M] [LawfulMonad M]

def EnforcesPurity : Prop :=
  ∀ {X : Type v} (mx : M X),
    (mx >>= fun x => pure (pure x)) = pure mx
  -- ∀ {X : Type v} (mx : M X),
  --   mx >>= (pure ∘ pure) = pure mx

theorem purity_implies_shape_eq_pure
  (h_pure : EnforcesPurity M) (mpu : M PUnit) : mpu = pure PUnit.unit := by
  have h1 := h_pure mpu
  have h2 := congrArg (fun (mmpu : M (M PUnit)) => mmpu >>= fun mpu => pure PUnit.unit) h1
  simp at h2
  exact h2

theorem purity_implies_subsingleton_shape
  (h_pure : EnforcesPurity M) : Subsingleton (M PUnit) := by
  constructor
  intro m1 m2
  rw [purity_implies_shape_eq_pure M h_pure m1, purity_implies_shape_eq_pure M h_pure m2]

-- The canonical embedding of `Type v` into `KleisliCat M`
def κΦ : Type v ⥤ KleisliCat M where
  obj X := X
  map f := fun x => pure (f x)
  map_id X := by
    ext x
    dsimp [CategoryStruct.id, KleisliCat.id_def]
    rfl
  map_comp f g := by
    ext x
    dsimp [CategoryStruct.comp, KleisliCat.comp_def, Bind.kleisliRight]
    rw [pure_bind]
    rfl

theorem functional_category_implies_enforces_purity
  (γη : 𝟭 (KleisliCat M) ⟶ (GEF_def (κΦ M)))
  (h_γη_app : ∀ Z, γη.app Z = fun z2mz_id => pure (fun _ => pure z2mz_id)) :
  EnforcesPurity M := by
  intro Z mz
  have h_nat := γη.naturality (X := PUnit) (Y := Z) (fun _ => mz)
  have h1 : (fun _ => mz) ≫ γη.app Z = γη.app PUnit ≫ (GEF_def (κΦ M)).map (fun _ => mz) := h_nat
  -- LHS Evaluation
  have h_lhs : ((fun _ => mz) ≫ γη.app Z) PUnit.unit =
    (mz >>= fun z => pure (fun _ : PUnit => pure z)) := by -- needed
    dsimp [CategoryStruct.comp, KleisliCat.comp_def, Bind.kleisliRight]
    rw [h_γη_app Z]
    rfl
  -- RHS Evaluation
  have h_rhs : (γη.app PUnit ≫ (GEF_def (κΦ M)).map (fun _ => mz)) PUnit.unit =
    pure (fun (_ : PUnit) => mz) := by -- needed
    change (γη.app PUnit PUnit.unit) >>= (GEF_def (κΦ M)).map (fun _ => mz) = _
    rw [h_γη_app]
    have h_map :
      (GEF_def (κΦ M)).map (fun (_ : PUnit.{v+1}) => mz) =
        fun pu2mz => pure (fun pu => pu2mz pu >>= fun pu => mz) := rfl
    rw [h_map]
    change
      (pure (fun _ => pure PUnit.unit)) >>= (fun pu2mu => pure (fun pu => pu2mu pu >>= fun pu => mz)) = _
    rw [pure_bind]
    change pure (fun (pu : PUnit) => pure PUnit.unit >>= fun pu => mz) = _ -- needed
    simp [pure_bind]
  have h2 : (mz >>= fun z => pure (fun _ => pure z)) = pure (fun (_ : PUnit.{v+1}) => mz) := by
    rw [← h_lhs, ← h_rhs]
    exact congrFun h1 PUnit.unit
  have h3 := congrArg (fun m_pu2mz => m_pu2mz >>= fun pu2mz => pure (pu2mz PUnit.unit)) h2
  -- LHS reduces to `mz >>= fun z => pure (pure z)`
  -- RHS reduces to `pure mz`
  simp at h3
  rw [← bind_pure_comp] at h3
  exact h3

-- A monad is idempotent if `fmap pure = pure` (i.e. Tη = ηT)
-- Note that the type system knows that the two `pure`s involved
-- are different ones from a type point of view
class IdempotentMonad (M : Type v → Type v) [Monad M] : Prop where
  idempotent : ∀ {X : Type v} (mx : M X),
    map pure mx = pure mx
    -- map (pure : X → M X) mx = (pure : M X → M (M X)) mx

-- 1. We can actually PROVE that EnforcesPurity is exactly IdempotentMonad!
theorem enforces_purity_is_idempotency (M : Type v → Type v) [Monad M] [LawfulMonad M] :
  EnforcesPurity M ↔ IdempotentMonad M := by
  constructor
  · intro h
    constructor
    intro X mx
    have h_bind : (mx >>= fun x => pure (pure x)) = map (fun x => (pure x : M X)) mx := by
      exact bind_pure_comp pure mx
    have h_pure := h mx
    rw [h_bind] at h_pure
    exact h_pure
  · intro h X mx
    have h_bind : (mx >>= fun x => pure (pure x)) = map (fun x => (pure x : M X)) mx := by
      exact bind_pure_comp pure mx
    rw [h_bind]
    exact h.idempotent mx

theorem enforces_purity_implies_naturality
  (h_pure : EnforcesPurity M)
  -- 1. Explicitly declare Z as an object of KleisliCat M
  (γη_app : (Z : KleisliCat M) → (Z ⟶ (GEF_def (κΦ M)).obj Z))
  -- 2. Use `show ... from ...` to cast the function to the correct morphism type
  (h_γη_app : ∀ (Z : KleisliCat M), γη_app Z = show Z → M (PUnit.{v+1} → M Z) from fun z => pure (fun _ : PUnit.{v+1} => pure z)) :
  ∀ {X Y : KleisliCat M} (f : X ⟶ Y),
    f ≫ γη_app Y = γη_app X ≫ (GEF_def (κΦ M)).map f := by

  intro X Y f
  ext x

  have h_lhs : (f ≫ γη_app Y) x = (f x >>= fun y => pure (fun _ : PUnit.{v+1} => pure y)) := by
    dsimp [CategoryStruct.comp, KleisliCat.comp_def, Bind.kleisliRight]
    rw [h_γη_app Y]
    rfl

  have h_rhs : (γη_app X ≫ (GEF_def (κΦ M)).map f) x = pure (fun _ : PUnit.{v+1} => f x) := by
    dsimp [CategoryStruct.comp, KleisliCat.comp_def, Bind.kleisliRight]
    rw [h_γη_app X]
    have h_map : (GEF_def (κΦ M)).map f = fun (g : PUnit.{v+1} → M X) => pure (fun pu => g pu >>= f) := by
      rfl
    rw [h_map]
    change (pure (fun _ : PUnit.{v+1} => pure x)) >>= (fun g => pure (fun pu => g pu >>= f)) = _
    rw [pure_bind]
    have h_inner : (fun (pu : PUnit.{v+1}) => pure x >>= f) = fun _ => f x := by
      funext pu
      rw [pure_bind]
    rw [h_inner]

  rw [h_lhs, h_rhs]
  let mx := f x
  change (mx >>= fun y => pure (fun _ : PUnit.{v+1} => pure y)) = pure (fun _ : PUnit.{v+1} => mx)

  have h1 := h_pure mx
  have h2 := congrArg (fun (mmy : M (M Y)) => mmy >>= fun my => pure (fun _ : PUnit.{v+1} => my)) h1

  -- 3. Add explicit type hints to `pure mx` to resolve the typeclass ambiguity
  have h_rhs_eq : ((pure mx : M (M Y)) >>= fun my => pure (fun _ : PUnit.{v+1} => my)) = pure (fun _ : PUnit.{v+1} => mx) := by
    rw [pure_bind]

  -- 3. Add explicit type hints to `pure (pure y : M Y)` to resolve the typeclass ambiguity
  have h_lhs_eq : ((mx >>= fun y => (pure (pure y : M Y) : M (M Y))) >>= fun my => pure (fun _ : PUnit.{v+1} => my)) =
                  (mx >>= fun y => pure (fun _ : PUnit.{v+1} => (pure y : M Y))) := by
    rw [bind_assoc]
    have h_inner2 : (fun (y : Y) => (pure (pure y : M Y) : M (M Y)) >>= fun my => pure (fun _ : PUnit.{v+1} => my)) =
                    (fun (y : Y) => pure (fun _ : PUnit.{v+1} => (pure y : M Y))) := by
      funext y
      rw [pure_bind]
    rw [h_inner2]

  rw [h_rhs_eq, h_lhs_eq] at h2
  exact h2


-- 2. Any Idempotent Monad on Type forces its shape at PUnit to be a Subsingleton.
--
-- Mathematical Justification:
-- The category of algebras of an idempotent monad is a full reflective subcategory.
-- Since full reflective subcategories are closed under limits, the terminal object
-- `PUnit` must belong to the subcategory, meaning it is perfectly reflected as itself.
-- Therefore `M PUnit ≃ PUnit`, making it a Subsingleton!

theorem idempotent_monad_implies_subsingleton_shape
  (M : Type v → Type v) [Monad M] [LawfulMonad M] [IdempotentMonad M] :
  Subsingleton (M PUnit) := by

  open IdempotentMonad in

  constructor
  intro a b

  have h_eq : ∀ y : M PUnit, y = pure PUnit.unit := by

    intro y

    have h1 : map id y = y := id_map y

    have h2 : @id PUnit = (fun _ => PUnit.unit) ∘ (pure : PUnit → M PUnit) := by
      funext x
      cases x
      rfl

    have step1 : y = map ((fun _ => PUnit.unit) ∘ (pure : PUnit → M PUnit)) y := by
      rw [← h2]
      exact h1.symm

    have step2 : map ((fun _ => PUnit.unit) ∘ (pure : PUnit → M PUnit)) y =
      map (fun _ => PUnit.unit) (map (pure : PUnit → M PUnit) y) := by
      exact comp_map (pure : PUnit → M PUnit) (fun _ => PUnit.unit) y

    have step3 : map (fun _ => PUnit.unit) (map (pure : PUnit → M PUnit) y) =
      map (fun _ => PUnit.unit) (pure y : M (M PUnit)) := by
      have hidem := idempotent y
      rw [hidem]

    have step4 : map (fun _ => PUnit.unit) (pure y : M (M PUnit)) = pure PUnit.unit := by
      exact map_pure (fun _ => PUnit.unit) y

    rw [step1, step2, step3, step4]

  rw [h_eq a, h_eq b]

-- 3. Therefore, the User's Conjecture formally holds for ALL monads!
theorem all_monads_purity_sieve
  (M : Type v → Type v) [Monad M] [LawfulMonad M] (h : EnforcesPurity M) :
  Subsingleton (M PUnit) := by
  -- Convert Purity to Idempotency using our proven theorem
  have h_idem : IdempotentMonad M := (enforces_purity_is_idempotency M).mp h
  -- Apply the category theory theorem
  exact idempotent_monad_implies_subsingleton_shape M

end PurityTheorem


end CoEndoYoneda
