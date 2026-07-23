import Mathlib.CategoryTheory.Yoneda
-- import Mathlib.CategoryTheory.Monad

set_option mathlib.tactic.category.grind true

namespace CoEndoYoneda

open CategoryTheory
open Opposite

universe u

-- CoYoneda Functor for X
abbrev CYF {C : Type (u + 1)} [LargeCategory.{u} C] (X : C) : C ⥤ Type u :=
  coyoneda.obj (op X)

-- CoYoneda EndoFunctor for X and Φ
abbrev CYEF_def {C : Type (u + 1)} [LargeCategory.{u} C] (Φ : Type u ⥤ C) (X : C) : C ⥤ C :=
  CYF X ⋙ Φ

-- Global EndoFunctor definition for Φ
abbrev GEF_def {C : Type (u + 1)} [LargeCategory.{u} C] (Φ : Type u ⥤ C) : C ⥤ C :=
  CYEF_def Φ (Φ.obj PUnit)

-- Global elements for Φ
abbrev G {C : Type (u + 1)} [LargeCategory.{u} C] (Φ : Type u ⥤ C) (X : C) : Type u :=
  Φ.obj PUnit ⟶ X

class FunctionalCategory (C : Type (u + 1)) extends LargeCategory.{u} C where
  -- Functional Functor
  Φ : Type u ⥤ C

  -- Global Multiplication
  γμ : (GEF_def Φ ⋙ GEF_def Φ) ⟶ GEF_def Φ

  -- Global Unit associativity law is not (yet) needed
  -- γ_assoc :
  --   ∀ (X : C), (GEF_def Φ).map (γμ.app X) ≫ γμ.app X = γμ.app ((GEF_def Φ).obj X) ≫ γμ.app X

  -- Global Unit
  γη : 𝟭 _ ⟶ GEF_def Φ

  -- Left Global Unit law
  γ_left_unit : ∀ (X : C), γη.app ((GEF_def Φ).obj X) ≫ γμ.app X = 𝟙 ((GEF_def Φ).obj X)

  -- Right Global Unit law is not (yet) needed
  -- γ_right_unit :
  --   ∀ (X : C), (GEF_def Φ).map (γη.app X) ≫ γμ.app X = 𝟙 ((GEF_def Φ).obj X)

  -- Functional Functor Map
  -- Note that we are into the `ConcreteCategory` realm now
  φ {X Y : Type u} (f : X → Y) : Φ.obj X ⟶ Φ.obj Y := Φ.map (TypeCat.ofHom f)

  -- Functional Functor Map equality
  φ_eq : ∀ {X Y : Type u} (f : X → Y), φ f = Φ.map (TypeCat.ofHom f) := by
    intros
    rfl

  -- relating γη and φ
  -- (also involves Φ.obj, recall that φ is defined in terms of Φ.map)
  γη_φ : ∀ (Z : Type u), γη.app (Φ.obj Z) = φ (fun z => φ (fun _ => z)) := by
    intros
    rfl

  -- not really needed
  -- GM : Monad C := {
  --   toFunctor := GEF_def Φ
  --   η := γη
  --   μ := γμ
  --   assoc := γ_assoc
  --   left_unit := γ_left_unit
  --   right_unit := γ_right_unit
  -- }

open FunctionalCategory

-- CoYoneda EndoFunctor
abbrev CYEF {C : Type (u + 1)} [FunctionalCategory C] (X : C) : C ⥤ C :=
  CYEF_def Φ X

-- Global EndoFunctor
abbrev GEF {C : Type (u + 1)} [FunctionalCategory C] : C ⥤ C :=
  GEF_def Φ

-- trivial FunctionalCategory instance
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

section CoEndoYonedaLemmas

open FunctionalCategory

variable {C : Type (u + 1)} [FunctionalCategory C]

abbrev Global : C → Type u := G Φ

-- Functor composition law for φ
@[simp]
theorem φ_comp {X Y Z : Type u} (f : X → Y) (g : Y → Z) :
    φ f ≫ φ g = (φ (C := C) (fun x => g (f x)) : Φ.obj X ⟶ Φ.obj Z) := by
  have h1 : φ (C := C) f = Φ.map (TypeCat.ofHom f) := φ_eq f
  have h2 : φ (C := C) g = Φ.map (TypeCat.ofHom g) := φ_eq g
  have h3 : φ (C := C) (fun x => g (f x)) = Φ.map (TypeCat.ofHom (fun x => g (f x))) := φ_eq _
  rw [h1, h2, h3, ← Φ.map_comp]
  rfl

-- Functor PUnit identity law for φ
@[simp]
theorem φ_pu_id (pu : PUnit) : φ (C := C) (fun _ => pu) = 𝟙 (Φ.obj PUnit) := by
  have h_pu_id : (fun _ => pu) = id := rfl
  have h_id_eq : φ (C := C) id = Φ.map (𝟙 PUnit) := by exact φ_eq id
  exact Eq.trans (congr_arg φ h_pu_id) (Eq.trans h_id_eq (Φ.map_id PUnit))

-- Equation relating CoYoneda EndoFunctor's (CYEF Z).map and φ
-- (recall that φ is defined in terms of Φ.map)
@[simp]
theorem CYEF_map_eq_φ {Z X Y : C} (f : X ⟶ Y) : (CYEF Z).map f = φ (. ≫ f) := by
  dsimp only [CYEF, CYEF_def, CYF, coyoneda, yoneda, Functor.comp_obj, Functor.comp_map]
  exact (φ_eq (. ≫ f)).symm

-- Equation relating  Global EndoFunctor's (GEF_def Φ).map and φ
-- (recall that φ is defined in terms of Φ.map)
@[simp]
theorem GF_map_eq_φ {X Y : C} (f : X ⟶ Y) : (GEF_def Φ).map f = φ (. ≫ f) :=
  CYEF_map_eq_φ f

-- given a natural transformation of type `CYEF X ⟶ (F ⋙ GEF)`
-- yields a global global value of type `Global (GEF.obj (F.obj X)))`
def globalTransformationToGlobalGlobalValue {F : C ⥤ C} {X : C} (τX : CYEF X ⟶ F ⋙ GEF) :
  Global ((F ⋙ GEF).obj X) := φ (fun _ => 𝟙 X) ≫ τX.app X

-- given a global global value of type `Global (GEF.obj (F.obj X)))`
-- yields a natural transformation of type `CYEF X ⟶ (F ⋙ GEF)`
@[simps]
def globalGlobalValueToGlobalTransformation
  {F : C ⥤ C} {X : C} (ggfx : Global (GEF.obj (F.obj X))) : CYEF X ⟶ (F ⋙ GEF) where
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

-- 'τZ' of type `CYEF Z ⟶ (F ⋙ GEF)`
-- can be defined in terms of global value 'φ (fun _ => 𝟙 Z) ≫ τX.app Z'
theorem left_inverse {F : C ⥤ C} {Z : C} (τX : CYEF Z ⟶ (F ⋙ GEF)) :
  τX =
    globalGlobalValueToGlobalTransformation (φ (fun _ => 𝟙 Z) ≫ τX.app Z) := by
  ext Y
  dsimp [globalGlobalValueToGlobalTransformation]
  have h_stepB :
    τX.app Y =
      (γη.app ((CYEF Z).obj Y) ≫ (GEF_def Φ).map (τX.app Y)) ≫ γμ.app (F.obj Y) := by
        grind [γ_left_unit (F.obj Y), γη.naturality (τX.app Y)]
  have h_γη_φ : γη.app ((CYEF Z).obj Y) = φ (fun w => φ (fun _ => w)) := γη_φ (Z ⟶ Y)
  have h_stepC : τX.app Y =
    (φ (fun f => φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => f)) ≫
      (GEF_def Φ).map (τX.app Y)) ≫
        γμ.app (F.obj Y) :=
          Eq.trans h_stepB
            (congr_arg (fun g => (g ≫ (GEF_def Φ).map (τX.app Y)) ≫ γμ.app (F.obj Y)) h_γη_φ)
  have h_stepD : τX.app Y =
    (φ (fun w => φ (fun _ => w)) ≫ φ (. ≫ τX.app Y)) ≫ γμ.app (F.obj Y) :=
      Eq.trans h_stepC
        (congr_arg (fun g => (φ (fun w => φ (fun _ => w)) ≫ g) ≫
          γμ.app (F.obj Y)) (GF_map_eq_φ (τX.app Y)))
  have h_φ_comp :
    φ (fun f => φ (fun _ => f)) ≫ φ (. ≫ τX.app Y) =
      φ (C := C) (fun f => φ (X := PUnit) (fun _ => f) ≫ τX.app Y) :=
        φ_comp _ _
  have h_stepE :
    τX.app Y =
      φ (fun f => φ (fun _ => f) ≫ τX.app Y) ≫ γμ.app (F.obj Y) :=
        Eq.trans h_stepD (congr_arg (. ≫ γμ.app (F.obj Y)) h_φ_comp)
  have h_inner_eq :
    φ (fun f => φ (fun _ => f) ≫ τX.app Y) =
      φ (C := C) ((φ (X := PUnit) (fun _ => 𝟙 Z) ≫ τX.app Z) ≫ (F ⋙ GEF).map .) := by
    congr 1
    ext f
    dsimp only
      [CYEF, CYEF_def, GEF, GEF_def, CYF, coyoneda, yoneda, Functor.comp_obj, Functor.comp_map]
    have step1 :
      (φ (fun _ => 𝟙 Z) ≫ τX.app Z) ≫ (F ⋙ GEF).map f =
        φ (X := PUnit) (fun _ => 𝟙 Z) ≫ (τX.app Z ≫ (F ⋙ GEF).map f) := Category.assoc _ _ _
    have step2 :
      φ (fun _ => 𝟙 Z) ≫ (τX.app Z ≫ (F ⋙ GEF).map f) =
        φ (fun _ => 𝟙 Z) ≫ ((CYEF Z).map f ≫ τX.app Y) :=
          congr_arg (φ (X := PUnit) (fun _ => 𝟙 Z) ≫ .) (τX.naturality f).symm
    have step3 :
      φ (fun _ => 𝟙 Z) ≫ ((CYEF Z).map f ≫ τX.app Y) =
        (φ (X := PUnit) (fun _ => 𝟙 Z) ≫ (CYEF Z).map f) ≫ τX.app Y := (Category.assoc _ _ _).symm
    have step4Helper :
      φ (fun _ => 𝟙 Z) ≫ (CYEF Z).map f =
        φ (X := PUnit) (fun _ => f) := by
          erw [CYEF_map_eq_φ f]
          have h_φ :
            φ (fun _ => 𝟙 Z) ≫ φ (. ≫ f) =
              φ (C := C) (X := PUnit) (fun _ => 𝟙 Z ≫ f) :=
                φ_comp (fun _ => 𝟙 Z) (. ≫ f)
          erw [h_φ]
          congr 1
          ext _
          exact Category.id_comp f
    have step4 :
      (φ (fun _ => 𝟙 Z) ≫ (CYEF Z).map f) ≫ τX.app Y =
        φ (fun _ => f) ≫ τX.app Y := congr_arg (. ≫ τX.app Y) step4Helper
    exact (Eq.trans step1 (Eq.trans step2 (Eq.trans step3 step4))).symm
  have h_final :
    τX.app Y =
      φ (fun f => (φ (fun _ => 𝟙 Z) ≫ τX.app Z) ≫ (F ⋙ GEF).map f) ≫ γμ.app (F.obj Y) :=
        Eq.trans h_stepE (congr_arg (. ≫ γμ.app (F.obj Y)) h_inner_eq)
  exact h_final

-- relating γμ and φ (also involves (GEF_def Φ).obj)
theorem φ_γμ {X : C} (ggfx : Global ((GEF_def Φ).obj X)) :
    φ (fun _ => ggfx) ≫ γμ.app X = ggfx := by
  have h_nat : ggfx ≫ γη.app ((GEF_def Φ).obj X) =
    γη.app (Φ.obj PUnit) ≫ (GEF_def Φ).map ggfx := γη.naturality ggfx
  erw [GF_map_eq_φ ggfx] at h_nat
  have h_γη : γη.app (Φ.obj PUnit) = φ (C := C) (fun pu => φ (fun _ => pu)) := γη_φ PUnit
  erw [h_γη] at h_nat
  have h_comp2 : φ (fun pu => φ (fun _ => pu)) ≫ φ (. ≫ ggfx) =
    φ (C := C) (Y := Global ((GEF_def Φ).obj X)) (fun pu => φ (fun _ => pu) ≫ ggfx) := φ_comp _ _
  erw [h_comp2] at h_nat
  have h_id_w : (fun pu => φ (fun _ => pu) ≫ ggfx) = (fun _ => ggfx) := by
    funext pu
    erw [φ_pu_id pu, Category.id_comp]
  have h_g_eta : ggfx ≫ γη.app ((GEF_def Φ).obj X) =
    φ (fun _ => ggfx) := by
      erw [h_id_w] at h_nat
      exact h_nat
  have h_left_unit : γη.app ((GEF_def Φ).obj X) ≫ γμ.app X = 𝟙 ((GEF_def Φ).obj X) := by
    exact γ_left_unit X
  have h_final : (ggfx ≫ γη.app ((GEF_def Φ).obj X)) ≫ γμ.app X =
    ggfx ≫ 𝟙 ((GEF_def Φ).obj X) := by
      erw [Category.assoc, h_left_unit]
  erw [Category.comp_id] at h_final
  erw [h_g_eta] at h_final
  exact h_final

theorem right_inverse {F : C ⥤ C} {X : C} :
  ∀ (ggfx : Global ((F ⋙ GEF).obj X)),
    ggfx =
      (fun τX => (φ fun _ => 𝟙 X) ≫ τX.app X) (globalGlobalValueToGlobalTransformation ggfx) :=
  fun (ggfx : Global ((F ⋙ GEF).obj X)) ↦ by
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

-- equivalence
def coEndoYonedaEquiv {F : C ⥤ C} {X : C} : (CYEF X ⟶ (F ⋙ GEF)) ≃ Global ((F ⋙ GEF).obj X)
where
  toFun     := globalTransformationToGlobalGlobalValue
  invFun    := globalGlobalValueToGlobalTransformation
  left_inv  := fun τX => (left_inverse  τX).symm
  right_inv := fun τX => (right_inverse τX).symm

/-

--
-- a less substantial lemma that does not use γμ
--

-- given a global value of type ` Global (F.obj X)`
-- yields a natural transformation of type `CYEF X ⟶ (F ⋙ GEF)`
@[simps]
def globalValueToGlobalTransformation {F : C ⥤ C} {X : C} (gfx : Global (F.obj X)) :
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

-- 'transformationToGlobalTransformation τX' with `τX` of type `CYEF X ⟶ F`
-- can be defined in terms of global value 'φ (fun _ => 𝟙 X) ≫ τX.app X'
theorem coEndoYonedaLemma {F : C ⥤ C} {X : C} (τX : CYEF X ⟶ F) :
  transformationToGlobalTransformation τX =
    globalValueToGlobalTransformation (φ (fun _ => 𝟙 X) ≫ τX.app X) := by
  ext Y
  dsimp [transformationToGlobalTransformation, globalValueToGlobalTransformation]
  erw [γη.naturality (τX.app Y)]
  erw [γη_φ (X ⟶ Y)]
  erw [GF_map_eq_φ (τX.app Y)]
  erw [φ_comp]
  congr 1
  ext f
  dsimp only [CYEF, CYEF_def, GEF, GEF_def, CYF, coyoneda, yoneda, Functor.comp_obj, Functor.comp_map]
  have step1 :
    (φ (fun _ => 𝟙 X) ≫ τX.app X) ≫ F.map f =
      φ (X := PUnit) (Y := X ⟶ X) (fun _ => 𝟙 X) ≫ (τX.app X ≫ F.map f) :=
        Category.assoc _ _ _
  have step2 :
    φ (fun _ => 𝟙 X) ≫ (τX.app X ≫ F.map f) = φ (fun _ => 𝟙 X) ≫ ((CYEF X).map f ≫ τX.app Y) :=
      congr_arg
        (φ (C := C) (X := PUnit) (Y := X ⟶ X) (fun _ => 𝟙 X) ≫ .) (τX.naturality f).symm
  have step3 :
    φ (fun _ => 𝟙 X) ≫ ((CYEF X).map f ≫ τX.app Y) =
      (φ (X := PUnit) (Y := X ⟶ X) (fun _ => 𝟙 X) ≫ (CYEF X).map f) ≫ τX.app Y :=
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
    (φ (fun _ => 𝟙 X) ≫ (CYEF X).map f) ≫ τX.app Y = φ (fun _ => f) ≫ τX.app Y :=
      congr_arg (. ≫ τX.app Y) step4Helper
  exact (Eq.trans step1 (Eq.trans step2 (Eq.trans step3 step4))).symm

-/

end CoEndoYonedaLemmas

end CoEndoYoneda
