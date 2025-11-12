Anna Williams, 30 October 2025

Definition of a displayed functor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Notation.UnderlyingType
open import UF.DependentEquality
open import UF.FunExt

module Categories.DisplayedCategories.DisplayedFunctor (fe : Fun-Ext) where

open import Categories.Type fe
open import Categories.Functor fe
open import Categories.DisplayedCategories.Type fe

record DisplayedFunctor {C : Precategory 𝓦 𝓣}
                        {C' : Precategory 𝓦' 𝓣'}
                        (F : Functor ⟨ C ⟩ ⟨ C' ⟩)
                        (D : DisplayedPrecategory 𝓤 𝓥 C)
                        (D' : DisplayedPrecategory 𝓤' 𝓥' C')
                      : (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥') ̇  where
 field
  obj-map : {c : obj ⟨ C ⟩}
          → (obj-fam {{D}}) c
          → (obj-fam {{D'}}) (Fobj {{F}} c)
  hom-map : {c c' : obj ⟨ C ⟩}
            {f : hom {{⟨ C ⟩}} c c'}
            {x : obj-fam {{D}} c}
            {y : obj-fam {{D}} c'}
          → hom-fam {{D}} f x y
          → hom-fam {{D'}} (Fhom {{F}} f) (obj-map x) (obj-map y)
  id-map-pres : {c : obj ⟨ C ⟩}
                {a : obj-fam {{D}} c}
              → hom-map (id-fam {{D}} a)
              ＝⟦ (λ v → hom-fam {{D'}} v _ _) , id-pres {{F}} c ⟧
                id-fam {{D'}} (obj-map a)
  map-distrib : {a b c : obj ⟨ C ⟩}
                {x : obj-fam {{D}} a}
                {y : obj-fam {{D}} b}
                {z : obj-fam {{D}} c}
                {f' : hom {{⟨ C ⟩}} a b}
                {g' : hom {{⟨ C ⟩}} b c}
                {f : hom-fam {{D}} f' x y}
                {g : hom-fam {{D}} g' y z}
              → hom-map (comp {{D}} g f)
              ＝⟦ (λ v → hom-fam {{D'}} v _ _) , distrib {{F}} g' f' ⟧
                comp {{D'}} (hom-map g) (hom-map f)

\end{code}
