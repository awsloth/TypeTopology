Anna Williams, 28 October 2025

Definition of a displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)
open import Notation.UnderlyingType
open import UF.Base
open import UF.DependentEquality
open import UF.Equiv hiding (_≅_ ; _≅⟨_⟩_)
open import UF.Sets
open import UF.Sets-Properties

module Categories.DisplayedCategories.Type where

open import Categories.Type 

\end{code}

We first define the notion of a displayed category. This is
exactly a category D and a functor F : D → C. Which satisfies
the usual structure of a category.

\begin{code}

record DisplayedPrecategory (𝓦 𝓨 : Universe) (C : Precategory 𝓤 𝓥) : ((𝓦 ⊔ 𝓨) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
 field
  obj-fam : (c : obj ⟨ C ⟩) → 𝓦 ̇
  hom-fam : {a b : obj ⟨ C ⟩}
            (f : hom {{⟨ C ⟩}} a b)
            (x : obj-fam a)
            (y : obj-fam b)
          → 𝓨 ̇
  hom-fam-is-set : {a b : obj ⟨ C ⟩}
                   {f : hom {{⟨ C ⟩ }} a b}
                   {x : obj-fam a}
                   {y : obj-fam b}
                 → is-set (hom-fam f x y)
  
  id-fam : {c : obj ⟨ C ⟩}
           (x : obj-fam c)
         → hom-fam (id {{⟨ C ⟩}} {c}) x x

  comp : {a b c : obj ⟨ C ⟩}
         {g : hom {{⟨ C ⟩}} b c}
         {f : hom {{⟨ C ⟩}} a b}
         {x : obj-fam a}
         {y : obj-fam b}
         {z : obj-fam c}
         (gyz : hom-fam g y z)
         (fxy : hom-fam f x y)
       → hom-fam (g ∘⟨ ⟨ C ⟩ ⟩ f) x z

  cmp-right-id : {a b : obj ⟨ C ⟩}
                 {f' : hom {{⟨ C ⟩}} a b}
                 {x : obj-fam a}
                 {y : obj-fam b}
                 (f : hom-fam f' x y)
               → comp f (id-fam x) ＝⟦ (λ - → hom-fam - x y) , right-id {{⟨ C ⟩}} f' ⟧ f

  cmp-left-id : {a b : obj ⟨ C ⟩}
                {f' : hom {{⟨ C ⟩}} a b}
                {x : obj-fam a}
                {y : obj-fam b}
                (f : hom-fam f' x y)
              → comp (id-fam y) f ＝⟦ (λ - → hom-fam - x y) , left-id {{⟨ C ⟩}} f' ⟧ f
  
  cmp-assoc : {a b c d : obj ⟨ C ⟩}
              {f' : hom {{⟨ C ⟩}} a b}
              {g' : hom {{⟨ C ⟩}} b c}
              {h' : hom {{⟨ C ⟩}} c d}
              {x : obj-fam a}
              {y : obj-fam b}
              {z : obj-fam c}
              {w : obj-fam d}
              {f : hom-fam f' x y}
              {g : hom-fam g' y z}
              {h : hom-fam h' z w}
            → comp h (comp g f) ＝⟦ (λ v → hom-fam v x w) , assoc {{⟨ C ⟩}} ⟧ comp (comp h g) f

open DisplayedPrecategory {{...}} public

\end{code}

We can now define a total precategory.

\begin{code}

TotalPrecategory : {𝓦 𝓨 : Universe} {C : Precategory 𝓤 𝓥} (D : DisplayedPrecategory 𝓦 𝓨 C) → Precategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
TotalPrecategory {𝓤} {𝓥} {𝓦} {𝓨} {C} D = (wildcategory , total-is-precategory)
 where
  wildcategory : WildCategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
  wildcategory = wildcat-make (Σ c ꞉ obj ⟨ C ⟩ , obj-fam {{D}} c)
                              (λ (a , x) (b , y) → Σ f ꞉ hom {{⟨ C ⟩}} a b , hom-fam {{D}} f x y)
                              (λ {(a , x)} → id {{⟨ C ⟩}} , id-fam {{D}} x)
                              (λ (g' , g) (f' , f) → (g' ∘⟨ ⟨ C ⟩ ⟩ f') , comp {{D}} g f)
                              (λ (f' , f) → to-Σ-＝ (left-id {{⟨ C ⟩}} f' , (Idtofun (dependent-Id-via-transport _ _)) (cmp-left-id {{D}} f)))
                              ((λ (f' , f) → to-Σ-＝ (right-id {{⟨ C ⟩}} f' , (Idtofun (dependent-Id-via-transport _ _)) (cmp-right-id {{D}} f))))
                              (to-Σ-＝ (assoc {{⟨ C ⟩}} , (Idtofun (dependent-Id-via-transport _ _)) (cmp-assoc {{D}})))

  total-is-precategory : is-precategory wildcategory
  total-is-precategory _ _ = Σ-is-set (hom-is-set {{C}}) (λ _ → hom-fam-is-set {{D}})

\end{code}
