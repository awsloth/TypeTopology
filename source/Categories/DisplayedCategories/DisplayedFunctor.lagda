Anna Williams, 30 October 2025

Definition of a displayed functor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Notation.UnderlyingType
open import UF.DependentEquality

module Categories.DisplayedCategories.DisplayedFunctor where

open import Categories.Type
open import Categories.Functor
open import Categories.DisplayedCategories.Type

record DisplayedFunctor {C : Precategory 𝓦 𝓣}
                        {C' : Precategory 𝓦' 𝓣'}
                        (F : Functor ⟨ C ⟩ ⟨ C' ⟩)
                        (D : DisplayedPrecategory 𝓤 𝓥 C)
                        (D' : DisplayedPrecategory 𝓤' 𝓥' C')
                      : (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥') ̇  where
 field
  obj-map : {c : obj ⟨ C ⟩}
          → (obj[_] {{D}}) c
          → (obj[_] {{D'}}) (Fobj {{F}} c)
  hom-map : {c c' : obj ⟨ C ⟩}
            {f : hom {{⟨ C ⟩}} c c'}
            {x : obj[_] {{D}} c}
            {y : obj[_] {{D}} c'}
          → hom[_] {{D}} f x y
          → hom[_] {{D'}} (Fhom {{F}} f) (obj-map x) (obj-map y)
  id-map-pres : {c : obj ⟨ C ⟩}
                {a : obj[_] {{D}} c}
              → hom-map (id-fam {{D}} a)
              ＝⟦ (λ v → hom[_] {{D'}} v _ _) , id-pres {{F}} c ⟧
                id-fam {{D'}} (obj-map a)
  map-distrib : {a b c : obj ⟨ C ⟩}
                {x : obj[_] {{D}} a}
                {y : obj[_] {{D}} b}
                {z : obj[_] {{D}} c}
                {f' : hom {{⟨ C ⟩}} a b}
                {g' : hom {{⟨ C ⟩}} b c}
                {f : hom[_] {{D}} f' x y}
                {g : hom[_] {{D}} g' y z}
              → hom-map (comp {{D}} g f)
              ＝⟦ (λ v → hom[_] {{D'}} v _ _) , distrib {{F}} g' f' ⟧
                comp {{D'}} (hom-map g) (hom-map f)

\end{code}
