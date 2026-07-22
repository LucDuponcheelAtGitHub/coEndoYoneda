import Mathlib.CategoryTheory.Yoneda
-- import Mathlib.CategoryTheory.Monad

namespace CoEndoYoneda

open CategoryTheory
open Opposite

universe u

-- CoYoneda Functor for X
abbrev CYF {C : Type (u + 1)} [LargeCategory.{u} C] (X : C) : C ⥤ Type u :=
  coyoneda.obj (op X)

-- CoYoneda EndoFunctor for X and T2C
abbrev CYEF_def {C : Type (u + 1)} [LargeCategory.{u} C] (T2C : Type u ⥤ C) (X : C) : C ⥤ C :=
  CYF X ⋙ T2C

-- Global EndoFunctor definition for T2C
abbrev GEF_def {C : Type (u + 1)} [LargeCategory.{u} C] (T2C : Type u ⥤ C) : C ⥤ C :=
  CYEF_def T2C (T2C.obj PUnit)

-- Global elements for T2C
abbrev G {C : Type (u + 1)} [LargeCategory.{u} C] (T2C : Type u ⥤ C) (X : C) : Type u :=
  T2C.obj PUnit ⟶ X

class FunctionalCategory (C : Type (u + 1)) extends LargeCategory.{u} C where
  -- Functional Functor
  Φ : Type u ⥤ C

  -- Global Multiplication
  γμ : GEF_def Φ ⋙ GEF_def Φ ⟶ GEF_def Φ

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
  --
  φ_eq : ∀ {X Y : Type u} (f : X → Y), φ f = Φ.map (TypeCat.ofHom f) := by intros; rfl

  γη_φ : ∀ (Z : Type u), γη.app (Φ.obj Z) = φ (fun z => φ (fun (_ : PUnit) => z)) :=
    by intros; rfl

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
    app := fun X => (𝟭 (Type u)).map (↾(fun (x : X) => ↾(fun _ : PUnit => x)))
    naturality := fun X Y f => by ext; rfl
  }

  γμ := {
    app :=
      fun X =>
        (𝟭 (Type u)).map
          (↾(fun (f : PUnit ⟶ PUnit ⟶ X) => ↾(fun p : PUnit => (f p) p)))
    naturality := fun X Y f => by ext; rfl
  }

  γ_left_unit := fun X => by rfl

section CoEndoYonedaLemmas

open FunctionalCategory

variable {C : Type (u + 1)} [FunctionalCategory C]

abbrev Global : C → Type u := G Φ

@[simp]
theorem φ_comp {X Y Z : Type u} (f : X → Y) (g : Y → Z) :
    φ f ≫ φ g = (φ (C := C) (fun x => g (f x)) : Φ.obj X ⟶ Φ.obj Z) := by
  have h1 : φ (C := C) f = Φ.map (TypeCat.ofHom f) := φ_eq f
  have h2 : φ (C := C) g = Φ.map (TypeCat.ofHom g) := φ_eq g
  have h3 : φ (C := C) (fun x => g (f x)) = Φ.map (TypeCat.ofHom (fun x => g (f x))) := φ_eq _
  rw [h1, h2, h3, ← Φ.map_comp]
  rfl

@[simp]
theorem CYEF_map_eq_φ {Z X Y : C} (f : X ⟶ Y) :
    (CYEF Z).map f = φ (C := C) (X := Z ⟶ X) (Y := Z ⟶ Y) (. ≫ f) := by
  dsimp only [CYEF, CYEF_def, CYF, coyoneda, yoneda, Functor.comp_obj, Functor.comp_map]
  exact (φ_eq (fun (h : Z ⟶ X) => h ≫ f)).symm

@[simp]
theorem GF_map_eq_φ {X Y : C} (f : X ⟶ Y) :
    (GEF_def Φ).map f = φ (C := C) (X := Global X) (Y := Global Y)
    (fun h => h ≫ f) :=
  CYEF_map_eq_φ f

@[simp]
theorem φ_const_id (pu : PUnit) :
    φ (C := C) (X := PUnit) (Y := PUnit) (fun _ => pu) = 𝟙 (Φ.obj PUnit) := by
  have h_pu_id : (fun (_ : PUnit) => pu) = id := rfl
  have h_id_eq : φ (C := C) (X := PUnit) (Y := PUnit) id = Φ.map (𝟙 PUnit) := by exact φ_eq id
  exact Eq.trans
    (congr_arg (fun (k : PUnit → PUnit) => φ (C := C) (X := PUnit) (Y := PUnit) k) h_pu_id)
    (Eq.trans h_id_eq (Φ.map_id PUnit))

@[simps]
def globalEndoTransformation {F : C ⥤ C} {X : C} (τ : CYEF X ⟶ F) : CYEF X ⟶ (F ⋙ GEF) where
  app Y := τ.app Y ≫ γη.app (F.obj Y)
  naturality _ _ h := by
    dsimp
    have h_nat := γη.naturality (F.map h)
    dsimp at h_nat
    erw [τ.naturality_assoc, h_nat]
    rw [Category.assoc]
    rfl

@[simps]
def globalFunctorialValueToNaturalTransformation1
  (F : C ⥤ C) {X : C} (g : Global (F.obj X)) : CYEF X ⟶ (F ⋙ GEF) where
  app Y := φ ((fun f => g ≫ F.map f) : (X ⟶ Y) → (Global (F.obj Y)))
  naturality _ _ h := by
    change Φ.map ((CYF X).map h) ≫ φ _ = φ _ ≫ Φ.map ((CYF (Φ.obj PUnit)).map (F.map h))
    rw [φ_eq, φ_eq]
    rw [← Φ.map_comp, ← Φ.map_comp]
    congr 1
    ext f
    change g ≫ F.map (f ≫ h) = (g ≫ F.map f) ≫ F.map h
    rw [F.map_comp, Category.assoc]

theorem coEndoYonedaLemma1 {F : C ⥤ C} {Z : C} (τ : CYEF Z ⟶ F) :
  globalEndoTransformation τ =
    globalFunctorialValueToNaturalTransformation1 F
      ((φ (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z)) ≫ τ.app Z) := by
  ext Y
  dsimp [globalEndoTransformation, globalFunctorialValueToNaturalTransformation1]
  erw [γη.naturality (τ.app Y)]
  erw [γη_φ (Z ⟶ Y)]
  erw [GF_map_eq_φ (τ.app Y)]
  erw [φ_comp]
  congr 1
  ext f
  dsimp only [CYEF, CYEF_def, GEF, GEF_def, CYF, coyoneda, yoneda, Functor.comp_obj, Functor.comp_map]
  have step1 : (φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫ τ.app Z) ≫ F.map f =
    φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫ (τ.app Z ≫ F.map f) :=
      Category.assoc _ _ _
  have step2 : φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫ (τ.app Z ≫ F.map f) =
    φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫ ((CYEF Z).map f ≫ τ.app Y) :=
      congr_arg
        (fun g => φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫ g) (τ.naturality f).symm
  have step3 : φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫ ((CYEF Z).map f ≫ τ.app Y) =
    (φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫ (CYEF Z).map f) ≫ τ.app Y :=
      (Category.assoc _ _ _).symm
  have step4Helper : φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫ (CYEF Z).map f =
    φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => f) := by
    erw [CYEF_map_eq_φ f]
    have h_φ : φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫
      φ (C := C) (X := Z ⟶ Z) (Y := Z ⟶ Y) (fun h => h ≫ f) =
        φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => 𝟙 Z ≫ f) :=
          φ_comp (fun _ => 𝟙 Z) (fun h => h ≫ f)
    erw [h_φ]
    congr 1
    ext _
    exact Category.id_comp f
  have step4 : (φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫ (CYEF Z).map f) ≫ τ.app Y =
    φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => f) ≫ τ.app Y :=
      congr_arg (fun g => g ≫ τ.app Y) step4Helper
  exact (Eq.trans step1 (Eq.trans step2 (Eq.trans step3 step4))).symm

@[simps]
def globalFunctorialValueToNaturalTransformation2
  (F : C ⥤ C) {X : C} (g : Global (GEF.obj (F.obj X))) : CYEF X ⟶ (F ⋙ GEF) where
  app Y :=
    φ ((fun f => g ≫ (F ⋙ GEF).map f) :
      (X ⟶ Y) → (Global (GEF.obj (F.obj Y)))) ≫ γμ.app (F.obj Y)
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
    change g ≫ GEF.map (F.map (f ≫ h)) = (g ≫ GEF.map (F.map f)) ≫ GEF.map (F.map h)
    rw [F.map_comp, GEF.map_comp, Category.assoc]

theorem coEndoYonedaLemma2 {F : C ⥤ C} {Z : C} (τ : CYEF Z ⟶ (F ⋙ GEF)) :
  τ =
    globalFunctorialValueToNaturalTransformation2 F
      ((φ (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z)) ≫ τ.app Z) := by
  ext Y
  dsimp [globalFunctorialValueToNaturalTransformation2]
  have h1 : τ.app Y = τ.app Y ≫ 𝟙 ((GEF_def Φ).obj (F.obj Y)) := (Category.comp_id (τ.app Y)).symm
  have h2 : 𝟙 ((GEF_def Φ).obj (F.obj Y)) = γη.app ((GEF_def Φ).obj (F.obj Y)) ≫ γμ.app (F.obj Y) :=
    (γ_left_unit (F.obj Y)).symm
  have h_left_unit : τ.app Y = τ.app Y ≫ (γη.app ((GEF_def Φ).obj (F.obj Y)) ≫ γμ.app (F.obj Y)) :=
    Eq.trans h1 (congr_arg (fun g => τ.app Y ≫ g) h2)
  have h_stepA : τ.app Y = (τ.app Y ≫ γη.app ((GEF_def Φ).obj (F.obj Y))) ≫ γμ.app (F.obj Y) :=
    Eq.trans h_left_unit (Category.assoc _ _ _).symm
  have h_nat_γη : τ.app Y ≫ γη.app ((GEF_def Φ).obj (F.obj Y)) =
    γη.app ((CYEF Z).obj Y) ≫ (GEF_def Φ).map (τ.app Y) :=
      γη.naturality (τ.app Y)
  have h_stepB : τ.app Y = (γη.app ((CYEF Z).obj Y) ≫ (GEF_def Φ).map (τ.app Y)) ≫ γμ.app (F.obj Y)
    := Eq.trans h_stepA (congr_arg (fun g => g ≫ γμ.app (F.obj Y)) h_nat_γη)
  have h_γη_φ : γη.app ((CYEF Z).obj Y) =
    φ (C := C) (X := Z ⟶ Y) (Y := Global (Φ.obj (Z ⟶ Y)))
      (fun w => φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => w)) :=
        γη_φ (Z ⟶ Y)
  have h_stepC : τ.app Y =
    (φ (C := C) (X := Z ⟶ Y) (Y := Global (Φ.obj (Z ⟶ Y)))
      (fun w => φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => w)) ≫
        (GEF_def Φ).map (τ.app Y)) ≫ γμ.app (F.obj Y) :=
          Eq.trans h_stepB
            (congr_arg (fun g => (g ≫ (GEF_def Φ).map (τ.app Y)) ≫ γμ.app (F.obj Y)) h_γη_φ)
  have h_stepD : τ.app Y =
    (φ (C := C) (X := Z ⟶ Y) (Y := Global (Φ.obj (Z ⟶ Y)))
      (fun w => φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => w)) ≫
        φ (C := C) (X := Global (Φ.obj (Z ⟶ Y))) (Y := Global ((F ⋙ GEF).obj Y))
          (fun k => k ≫ τ.app Y)) ≫ γμ.app (F.obj Y) :=
            Eq.trans h_stepC (congr_arg
              (fun g => (φ (C := C) (X := Z ⟶ Y) (Y := Global (Φ.obj (Z ⟶ Y)))
                (fun w => φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => w)) ≫ g) ≫
                  γμ.app (F.obj Y)) (GF_map_eq_φ (τ.app Y)))
  have h_φ_comp : φ (C := C) (X := Z ⟶ Y) (Y := Global (Φ.obj (Z ⟶ Y)))
    (fun w => φ (C := C) (X := PUnit) (Y := Z ⟶ Y)
      (fun _ => w)) ≫
        φ (C := C) (X := Global (Φ.obj (Z ⟶ Y))) (Y := Global ((F ⋙ GEF).obj Y))
          (fun k => k ≫ τ.app Y) = φ (C := C) (X := Z ⟶ Y) (Y := Global ((F ⋙ GEF).obj Y))
            (fun f => φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => f) ≫ τ.app Y) :=
              φ_comp _ _
  have h_stepE : τ.app Y = φ (C := C) (X := Z ⟶ Y) (Y := Global ((F ⋙ GEF).obj Y))
    (fun f => φ (C := C) (X := PUnit) (Y := Z ⟶ Y)
      (fun _ => f) ≫ τ.app Y) ≫ γμ.app (F.obj Y) :=
        Eq.trans h_stepD (congr_arg (fun g => g ≫ γμ.app (F.obj Y)) h_φ_comp)
  have h_inner_eq : φ (C := C) (X := Z ⟶ Y) (Y := Global ((F ⋙ GEF).obj Y))
    (fun f => φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => f) ≫ τ.app Y) =
      φ (C := C) (X := Z ⟶ Y) (Y := Global ((F ⋙ GEF).obj Y))
        (fun f => (φ (C := C) (X := PUnit) (Y := Z ⟶ Z)
          (fun _ => 𝟙 Z) ≫ τ.app Z) ≫ (F ⋙ GEF).map f) := by
    congr 1
    ext f
    dsimp only
      [CYEF, CYEF_def, GEF, GEF_def, CYF, coyoneda, yoneda, Functor.comp_obj, Functor.comp_map]
    have step1 : (φ (C := C) (X := PUnit) (Y := Z ⟶ Z)
      (fun _ => 𝟙 Z) ≫ τ.app Z) ≫ (F ⋙ GEF).map f = φ (C := C) (X := PUnit) (Y := Z ⟶ Z)
        (fun _ => 𝟙 Z) ≫ (τ.app Z ≫ (F ⋙ GEF).map f) := Category.assoc _ _ _
    have step2 : φ (C := C) (X := PUnit) (Y := Z ⟶ Z)
      (fun _ => 𝟙 Z) ≫ (τ.app Z ≫ (F ⋙ GEF).map f) = φ (C := C) (X := PUnit) (Y := Z ⟶ Z)
        (fun _ => 𝟙 Z) ≫ ((CYEF Z).map f ≫ τ.app Y) :=
          congr_arg (fun g => φ (C := C) (X := PUnit) (Y := Z ⟶ Z)
            (fun _ => 𝟙 Z) ≫ g) (τ.naturality f).symm
    have step3 : φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫ ((CYEF Z).map f ≫ τ.app Y)
      = (φ (C := C) (X := PUnit) (Y := Z ⟶ Z) (fun _ => 𝟙 Z) ≫
          (CYEF Z).map f) ≫ τ.app Y := (Category.assoc _ _ _).symm
    have step4Helper : φ (C := C) (X := PUnit) (Y := Z ⟶ Z)
      (fun _ => 𝟙 Z) ≫ (CYEF Z).map f = φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => f) := by
      erw [CYEF_map_eq_φ f]
      have h_φ : φ (C := C) (X := PUnit) (Y := Z ⟶ Z)
        (fun _ => 𝟙 Z) ≫ φ (C := C) (X := Z ⟶ Z) (Y := Z ⟶ Y)
          (fun h => h ≫ f) = φ (C := C) (X := PUnit) (Y := Z ⟶ Y) (fun _ => 𝟙 Z ≫ f) :=
            φ_comp (fun _ => 𝟙 Z) (fun h => h ≫ f)
      erw [h_φ]
      congr 1
      ext _
      exact Category.id_comp f
    have step4 : (φ (C := C) (X := PUnit) (Y := Z ⟶ Z)
    (fun _ => 𝟙 Z) ≫ (CYEF Z).map f) ≫ τ.app Y = φ (C := C) (X := PUnit) (Y := Z ⟶ Y)
      (fun _ => f) ≫ τ.app Y := congr_arg (fun g => g ≫ τ.app Y) step4Helper
    exact (Eq.trans step1 (Eq.trans step2 (Eq.trans step3 step4))).symm
  have h_final : τ.app Y = φ (C := C) (X := Z ⟶ Y) (Y := Global ((F ⋙ GEF).obj Y))
    (fun f => (φ (C := C) (X := PUnit) (Y := Z ⟶ Z)
      (fun _ => 𝟙 Z) ≫ τ.app Z) ≫ (F ⋙ GEF).map f) ≫ γμ.app (F.obj Y) :=
        Eq.trans h_stepE (congr_arg (fun g => g ≫ γμ.app (F.obj Y)) h_inner_eq)
  exact h_final

@[simp]
theorem φ_const_comp_γμ {W : C} (g : Global ((GEF_def Φ).obj W)) :
  φ (C := C) (X := PUnit) (Y := Global ((GEF_def Φ).obj W)) (fun _ => g) ≫ γμ.app W = g := by
  have h_nat : g ≫ γη.app ((GEF_def Φ).obj W) =
    γη.app (Φ.obj PUnit) ≫ (GEF_def Φ).map g := γη.naturality g
  erw [GF_map_eq_φ g] at h_nat
  have h_γη : γη.app (Φ.obj PUnit) =
    φ (C := C) (X := PUnit) (Y := Global (Φ.obj PUnit))
      (fun w => φ (C := C) (X := PUnit) (Y := PUnit) (fun _ => w)) := γη_φ PUnit
  erw [h_γη] at h_nat
  have h_comp2 : φ (C := C) (X := PUnit) (Y := Global (Φ.obj PUnit))
    (fun w => φ (C := C) (X := PUnit) (Y := PUnit) (fun _ => w)) ≫
      φ (C := C) (X := Global (Φ.obj PUnit)) (Y := Global ((GEF_def Φ).obj W))
        (fun k => k ≫ g) =
    φ (C := C) (X := PUnit) (Y := Global ((GEF_def Φ).obj W))
      (fun w => φ (C := C) (X := PUnit) (Y := PUnit) (fun _ => w) ≫ g) := φ_comp _ _
  erw [h_comp2] at h_nat
  have h_id_w : (fun (w : PUnit) => φ (C := C) (X := PUnit) (Y := PUnit)
    (fun _ => w) ≫ g) = (fun _ => g) := by
    funext w
    erw [φ_const_id w, Category.id_comp]
  have h_g_eta : g ≫ γη.app ((GEF_def Φ).obj W) =
    φ (C := C) (X := PUnit) (Y := Global ((GEF_def Φ).obj W)) (fun _ => g) := by
    erw [h_id_w] at h_nat
    exact h_nat
  have h_left_unit : γη.app ((GEF_def Φ).obj W) ≫ γμ.app W = 𝟙 ((GEF_def Φ).obj W) := by
    exact γ_left_unit W
  have h_final2 : (g ≫ γη.app ((GEF_def Φ).obj W)) ≫ γμ.app W = g ≫ 𝟙 ((GEF_def Φ).obj W) := by
    erw [Category.assoc, h_left_unit]
  erw [Category.comp_id] at h_final2
  erw [h_g_eta] at h_final2
  exact h_final2

def coEndoYonedaEquiv {F : C ⥤ C} {X : C} : (CYEF X ⟶ (F ⋙ GEF)) ≃ (Global ((F ⋙ GEF).obj X))
where
  toFun τ := (φ (X := PUnit) (Y := X ⟶ X) (fun _ => 𝟙 X)) ≫ τ.app X
  invFun g := globalFunctorialValueToNaturalTransformation2 F g
  left_inv := fun τ ↦ (coEndoYonedaLemma2 τ).symm
  right_inv := fun g ↦ by
    change φ (C := C) (X := PUnit) (Y := X ⟶ X) (fun _ => 𝟙 X) ≫
      (φ (C := C) (X := X ⟶ X) (Y := Global (GEF.obj (F.obj X))) (fun f => g ≫ (F ⋙ GEF).map f) ≫
        γμ.app (F.obj X)) = g
    rw [← Category.assoc]
    have h1 : φ (C := C) (X := PUnit) (Y := X ⟶ X) (fun _ => 𝟙 X) ≫
      φ (C := C) (X := X ⟶ X) (Y := Global (GEF.obj (F.obj X))) (fun f => g ≫ (F ⋙ GEF).map f) =
      φ (C := C) (X := PUnit) (Y := Global (GEF.obj (F.obj X))) (fun _ => g ≫ (F ⋙ GEF).map (𝟙 X)) := φ_comp _ _
    rw [h1]
    have h2 : φ (C := C) (X := PUnit) (Y := Global (GEF.obj (F.obj X))) (fun _ => g ≫ (F ⋙ GEF).map (𝟙 X)) =
      φ (C := C) (X := PUnit) (Y := Global (GEF.obj (F.obj X))) (fun _ => g) := by
      congr 1
      ext _
      exact Eq.trans (congr_arg (fun k => g ≫ k) ((F ⋙ GEF).map_id X)) (Category.comp_id g)
    rw [h2]
    exact φ_const_comp_γμ g

end CoEndoYonedaLemmas

end CoEndoYoneda
